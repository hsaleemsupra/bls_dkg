// Copyright (c) 2022, MaidSafe.
// All rights reserved.
//
// This SAFE Network Software is licensed under the BSD-3-Clause license.
// Please see the LICENSE file for more details.

use std::borrow::Borrow;
use crate::dev_utils::{create_ids, PeerId};
use crate::key_gen::{message::Message, Error, KeyGen, MessageAndTarget};
use anyhow::{format_err, Result};
use bincode::serialize;
use blsttc::{PublicKey, PublicKeySet, SignatureShare};
use itertools::Itertools;
use rand::{Rng, RngCore};
use std::collections::{BTreeMap, BTreeSet};
use blsttc::blstrs::G1Projective;
use blsttc::group::Group;
use blsttc::poly::Poly;
use xor_name::XorName;


// Alter the configure of the number of nodes and the threshold.
const CLANS_PER_TRIBE: usize = 5;
const NODES_PER_CLAN: usize = 5;
const TRIBE_THRESHOLD: usize = 2;
const CLAN_THRESHOLD: usize = 2;


fn setup_generators<R: RngCore>(
    mut rng: &mut R,
    non_responsives: BTreeSet<u64>,
) -> Result<(Vec<PeerId>, Vec<KeyGen>)> {
    // Generate individual ids.
    let peer_ids: Vec<PeerId> = create_ids(CLANS_PER_TRIBE*NODES_PER_CLAN);

    Ok((
        peer_ids.clone(),
        create_generators(&mut rng, non_responsives, &peer_ids)?,
    ))
}

fn create_generators<R: RngCore>(
    mut rng: &mut R,
    non_responsives: BTreeSet<u64>,
    peer_ids: &[PeerId]
) -> Result<Vec<KeyGen>> {
    // Generate individual key pairs.
    let mut tribe: Vec<BTreeSet<XorName>> = Vec::new();

    // needed for pedersen commitments
    // This h needs to be generated in a secure manner and same value of h is given to each node
    // For now h is generated using a random number, however later we want to change it to h = H(g||i)
    //todo: Change generation of h to use hashing.
    let h = G1Projective::random(&mut rng);

    // Creating a tribe using PeerIds
    for i in 0..CLANS_PER_TRIBE{
        let mut clan: BTreeSet<XorName> = BTreeSet::new();
        for j in 0..NODES_PER_CLAN{
            clan.insert(peer_ids[i*NODES_PER_CLAN + j].name());
        }
        tribe.push(clan);
    }


    // Create the `KeyGen` instances
    let mut generators = Vec::new();
    let mut proposals = Vec::new();
    for peer_id in peer_ids.iter() {
        let key_gen = {
            let (key_gen, messaging) =
                match KeyGen::initialize(peer_id.name(), CLANS_PER_TRIBE, TRIBE_THRESHOLD, NODES_PER_CLAN, CLAN_THRESHOLD, tribe.clone(), h) {
                    Ok(result) => result,
                    Err(err) => {
                        return Err(format_err!(
                            "Failed to initialize KeyGen of {:?} {:?}",
                            &peer_id,
                            err
                        ))
                    }
                };
            proposals.extend(messaging);
            key_gen
        };

        generators.push(key_gen);
    }

    messaging(&mut rng, &mut generators, &mut proposals, non_responsives);

    Ok(generators)
}

fn messaging<R: RngCore>(
    mut rng: &mut R,
    generators: &mut [KeyGen],
    proposals: &mut Vec<MessageAndTarget>,
    non_responsives: BTreeSet<u64>,
) {
    // Simulating the AE pattern
    let mut cached_msg = BTreeMap::<XorName, Message>::new();

    // Keep broadcasting the proposals among the generators till no more.
    // The proposal from non_responsive nodes shall be ignored.
    while !proposals.is_empty() {
        let proposals_local = std::mem::take(proposals);
        for (receiver, proposal) in &proposals_local {
            match proposal {
                Message::Initialization { .. } | Message::Proposal { .. } => {
                    let _ = cached_msg.insert(proposal.id(), proposal.clone());
                }
                _ => {}
            }
            for (index, generator) in generators.iter_mut().enumerate() {
                if receiver == &generator.our_id {
                    let messaging_vec = if let Ok(messaging_vec) =
                        generator.handle_message(&mut rng, proposal.clone())
                    {
                        messaging_vec
                    } else {
                        let mut messages: Vec<Message> = cached_msg.values().cloned().collect();
                        messages.push(proposal.clone());
                        let (messaging_vec, _unhandable) =
                            generator.handle_pre_session_messages(&mut rng, messages);
                        messaging_vec
                    };
                    if !non_responsives.contains(&(index as u64)) {
                        messaging_vec
                            .iter()
                            .for_each(|prop| proposals.push(prop.clone()));
                    }
                }
            }
        }
    }
}

#[test]
fn all_nodes_being_responsive() -> Result<()> {
    let mut rng = rand::thread_rng();
    let (peer_ids, mut generators) = setup_generators(&mut rng, BTreeSet::new())?;

    // We need to call timed phase transition 4 times to move from:
    // 1. pedersen contributing phase to pedersen complaining phase
    // 2. pedersen complaining phase to feldman contribution phase
    // 3. feldman contribution phase to feldman complaining phase
    // 4. feldman complaining phase to finalization phase
    // and then call the key generating procedure

    let mut proposals = Vec::new();
    for _ in 0..4 {
        peer_ids.iter().enumerate().for_each(|(index, _peer_id)| {
            if let Ok(proposal_vec) = generators[index].timed_phase_transition(&mut rng) {

                for proposal in proposal_vec {
                    proposals.push(proposal);
                }

            }
        });

        messaging(
            &mut rng,
            &mut generators,
            &mut proposals,
            BTreeSet::new(),
        );
        assert!(proposals.is_empty());
    };


    //Generating keys
    /*assert!(generators
        .iter_mut()
        .all(|key_gen| key_gen.generate_keys().is_some()));*/


    //Testing Signature generation and verification

    let msg = "Test message!";

    let mut clan_signatures: BTreeMap<usize, SignatureShare> = BTreeMap::new();
    let mut clan_public_keys = Vec::new();

    // generating and verifying signatures in clans
    for i in 0..CLANS_PER_TRIBE{

        let pub_key_set: PublicKeySet = generators[i*NODES_PER_CLAN]
            .generate_keys()
            .expect("Failed to generate `PublicKeySet` for node #0")
            .1
            .public_key_set;

        let mut sig_shares: BTreeMap<usize, SignatureShare> = BTreeMap::new();

        for j in 0..NODES_PER_CLAN{

            let outcome = if let Some(outcome) = generators[i*NODES_PER_CLAN + j].generate_keys() {
                outcome.1
            } else {
                return Err(format_err!(
                    "Failed to generate `PublicKeySet` and `SecretKeyShare` for node #{}, {}",
                    i+1, j+1
                ));
            };

            let sk = outcome.secret_key_share;
            let index = generators[i*NODES_PER_CLAN + j].our_index.1 as usize;
            let pks = outcome.public_key_set;
            assert_eq!(pks, pub_key_set);
            let sig = sk.sign(msg);
            assert!(pks.public_key_share(index).verify(&sig, msg));
            let _ = sig_shares.insert(index, sig);

        }

        let sig = match pub_key_set.combine_signatures(sig_shares.iter()) {
            Ok(sig) => sig,
            Err(e) => return Err(format_err!("Unexpected Error {:?}: Not able to generate Signature with THRESHOLD + 1 sig_shares", e)),
        };

        assert!(pub_key_set.public_key().verify(&sig, msg));

        let clan_idx = generators[i*NODES_PER_CLAN].our_index.0 as usize;
        let _ = clan_signatures.insert(clan_idx, SignatureShare(sig));

        clan_public_keys.push((i, pub_key_set.public_key_G1()));

    }


    // aggregating and verifying tribe level signature

    let tribe_public_key_g1 = crate::blsttc::interpolate(TRIBE_THRESHOLD-1, clan_public_keys).expect("wrong number of values");
    let tribe_public_key: PublicKey = tribe_public_key_g1.into();

    let rand_poly: Poly = Poly::random(TRIBE_THRESHOLD-1, &mut rng);
    let rand_public_key: PublicKeySet =  rand_poly.commitment().into();

    let tribe_signature = match rand_public_key.combine_signatures(clan_signatures.iter()) {
        Ok(sig) => sig,
        Err(e) => return Err(format_err!("Unexpected Error {:?}: Not able to generate Signature with THRESHOLD + 1 sig_shares", e)),
    };

    assert!(tribe_public_key.verify(&tribe_signature, msg));


    Ok(())

}


#[test]
fn having_max_unresponsive_nodes_still_work() -> Result<()> {
    let mut rng = rand::thread_rng();

    let mut rand_non_resp_nodes_combination = BTreeSet::new();

    let mut start: u64 = 0;
    let mut end: u64 = NODES_PER_CLAN as u64;

    // creating a list of non-responsive nodes by taking at most NODES_PER_CLAN - CLAN_THRESHOLD - 1
    // non-responsive nodes from each clan.

    for _i in 0..CLANS_PER_TRIBE{
        let all_nodes: BTreeSet<_> = (start..end).collect();

        //taking the first combination only
        let combinations_of_non_resp = all_nodes
            .iter()
            .cloned()
            .combinations(NODES_PER_CLAN - CLAN_THRESHOLD - 1).take(1);


        for non_reps in combinations_of_non_resp{
            rand_non_resp_nodes_combination.append(&mut non_reps.iter().cloned().collect());
        }

        start = end;
        end = end + NODES_PER_CLAN as u64;


    }


    let non_responsives: BTreeSet<u64> = rand_non_resp_nodes_combination.clone();
    let (peer_ids, mut generators) = setup_generators(&mut rng, non_responsives.clone())?;

    let mut proposals = Vec::new();


    // We need to call timed phase transition 4 times to move from:
    // 1. pedersen contributing phase to pedersen complaining phase
    // 2. pedersen complaining phase to feldman contribution phase
    // 3. feldman contribution phase to feldman complaining phase
    // 4. feldman complaining phase to finalization phase
    // and then call the key generating procedure

    for _ in 0..5 {
        peer_ids.iter().enumerate().for_each(|(index, _peer_id)| {
            if let Ok(proposal_vec) = generators[index].timed_phase_transition(&mut rng) {
                if !non_responsives.contains(&(index as u64)) {
                    for proposal in proposal_vec {
                        proposals.push(proposal);
                    }
                }
            }
        });
        // Continue the procedure with messaging.
        messaging(
            &mut rng,
            &mut generators,
            &mut proposals,
            non_responsives.clone(),
        );
        assert!(proposals.is_empty());
    }




    let all_nodes: BTreeSet<_> = (0u64..(NODES_PER_CLAN*CLANS_PER_TRIBE) as u64).collect();
    let responsive = all_nodes
        .difference(&non_responsives)
        .cloned()
        .collect_vec();


    let msg = "Test message!";
    let mut clan_signatures: BTreeMap<usize, SignatureShare> = BTreeMap::new();
    let mut clan_public_keys = Vec::new();

    // generating and verifying signatures in clans
    for i in 0..CLANS_PER_TRIBE{

        let pub_key_set: PublicKeySet = generators[ responsive[i* (NODES_PER_CLAN - CLAN_THRESHOLD)] as usize]
            .generate_keys()
            .expect("Failed to generate `PublicKeySet` for node #0")
            .1
            .public_key_set;

        let mut sig_shares: BTreeMap<usize, SignatureShare> = BTreeMap::new();

        for j in 0..NODES_PER_CLAN{

            let index = i * NODES_PER_CLAN + j;

            if !non_responsives.contains(&(index as u64)) {
                let outcome = if let Some(outcome) = generators[i * NODES_PER_CLAN + j].generate_keys() {
                    outcome.1
                } else {
                    return Err(format_err!(
                    "Failed to generate `PublicKeySet` and `SecretKeyShare` for node #{}, {}",
                    i+1, j+1
                ));
                };

                let sk = outcome.secret_key_share;
                let index = generators[i * NODES_PER_CLAN + j].our_index.1 as usize;
                let pks = outcome.public_key_set;
                assert_eq!(pks, pub_key_set);
                let sig = sk.sign(msg);
                assert!(pks.public_key_share(index).verify(&sig, msg));
                let _ = sig_shares.insert(index, sig);
            }
            else {
                assert!(generators[i * NODES_PER_CLAN + j].generate_keys().is_none());
            }

        }

        let sig = match pub_key_set.combine_signatures(sig_shares.iter()) {
            Ok(sig) => sig,
            Err(e) => return Err(format_err!("Unexpected Error {:?}: Not able to generate Signature with THRESHOLD + 1 sig_shares", e)),
        };

        assert!(pub_key_set.public_key().verify(&sig, msg));

        let clan_idx = generators[i*NODES_PER_CLAN].our_index.0 as usize;
        let _ = clan_signatures.insert(clan_idx, SignatureShare(sig));

        clan_public_keys.push((i, pub_key_set.public_key_G1()));

    }


    // aggregating and verifying tribe level signature

    let tribe_public_key_g1 = crate::blsttc::interpolate(TRIBE_THRESHOLD-1, clan_public_keys).expect("wrong number of values");
    let tribe_public_key: PublicKey = tribe_public_key_g1.into();

    let rand_poly: Poly = Poly::random(TRIBE_THRESHOLD-1, &mut rng);
    let rand_public_key: PublicKeySet =  rand_poly.commitment().into();

    let tribe_signature = match rand_public_key.combine_signatures(clan_signatures.iter()) {
        Ok(sig) => sig,
        Err(e) => return Err(format_err!("Unexpected Error {:?}: Not able to generate Signature with THRESHOLD + 1 sig_shares", e)),
    };

    assert!(tribe_public_key.verify(&tribe_signature, msg));


    Ok(())
}




#[test]
fn having_max_unresponsive_nodes_in_feldman_still_work() -> Result<()> {
    let mut rng = rand::thread_rng();

    let mut rand_non_resp_nodes_combination = BTreeSet::new();

    let mut start: u64 = 0;
    let mut end: u64 = NODES_PER_CLAN as u64;

    // creating a list of non-responsive nodes by taking at most NODES_PER_CLAN - CLAN_THRESHOLD - 1
    // non-responsive nodes from each clan.

    for _i in 0..CLANS_PER_TRIBE{
        let all_nodes: BTreeSet<_> = (start..end).collect();

        //taking the first combination only
        let combinations_of_non_resp = all_nodes
            .iter()
            .cloned()
            .combinations(NODES_PER_CLAN - CLAN_THRESHOLD - 1).take(1);


        for non_reps in combinations_of_non_resp{
            rand_non_resp_nodes_combination.append(&mut non_reps.iter().cloned().collect());
        }

        start = end;
        end = end + NODES_PER_CLAN as u64;


    }


    let non_responsives: BTreeSet<u64> = rand_non_resp_nodes_combination.clone();
    let (peer_ids, mut generators) = setup_generators(&mut rng, BTreeSet::new())?;

    let mut proposals = Vec::new();

    // All nodes contribute for Pedersen-VSS
    // So we transform from pedersen contributing phase to pedersen complaining phase
    peer_ids.iter().enumerate().for_each(|(index, _peer_id)| {
        if let Ok(proposal_vec) = generators[index].timed_phase_transition(&mut rng) {

            for proposal in proposal_vec {
                proposals.push(proposal);
            }

        }
    });

    messaging(
        &mut rng,
        &mut generators,
        &mut proposals,
        BTreeSet::new(),
    );
    assert!(proposals.is_empty());


    // Since we have no complaints, we move to Feldman_Contribution Phase
    // Here we introduce non-contributers.
    // However, all of the nodes can reconstruct the polynomial using shares

    for _ in 0..4 {
        peer_ids.iter().enumerate().for_each(|(index, _peer_id)| {
            if let Ok(proposal_vec) = generators[index].timed_phase_transition(&mut rng) {
                if !non_responsives.contains(&(index as u64)) {
                    for proposal in proposal_vec {
                        proposals.push(proposal);
                    }
                }
            }
        });
        // Continue the procedure with messaging.
        messaging(
            &mut rng,
            &mut generators,
            &mut proposals,
            non_responsives.clone(),
        );
        assert!(proposals.is_empty());
    }

    //Testing Signature generation and verification

    let msg = "Test message!";

    let mut clan_signatures: BTreeMap<usize, SignatureShare> = BTreeMap::new();
    let mut clan_public_keys = Vec::new();

    // generating and verifying signatures in clans
    for i in 0..CLANS_PER_TRIBE{

        let pub_key_set: PublicKeySet = generators[i*NODES_PER_CLAN]
            .generate_keys()
            .expect("Failed to generate `PublicKeySet` for node #0")
            .1
            .public_key_set;

        let mut sig_shares: BTreeMap<usize, SignatureShare> = BTreeMap::new();

        for j in 0..NODES_PER_CLAN{

            let outcome = if let Some(outcome) = generators[i*NODES_PER_CLAN + j].generate_keys() {
                outcome.1
            } else {
                return Err(format_err!(
                    "Failed to generate `PublicKeySet` and `SecretKeyShare` for node #{}, {}",
                    i+1, j+1
                ));
            };

            let sk = outcome.secret_key_share;
            let index = generators[i*NODES_PER_CLAN + j].our_index.1 as usize;
            let pks = outcome.public_key_set;
            assert_eq!(pks, pub_key_set);
            let sig = sk.sign(msg);
            assert!(pks.public_key_share(index).verify(&sig, msg));
            let _ = sig_shares.insert(index, sig);

        }

        let sig = match pub_key_set.combine_signatures(sig_shares.iter()) {
            Ok(sig) => sig,
            Err(e) => return Err(format_err!("Unexpected Error {:?}: Not able to generate Signature with THRESHOLD + 1 sig_shares", e)),
        };

        assert!(pub_key_set.public_key().verify(&sig, msg));

        let clan_idx = generators[i*NODES_PER_CLAN].our_index.0 as usize;
        let _ = clan_signatures.insert(clan_idx, SignatureShare(sig));

        clan_public_keys.push((i, pub_key_set.public_key_G1()));

    }


    // aggregating and verifying tribe level signature

    let tribe_public_key_g1 = crate::blsttc::interpolate(TRIBE_THRESHOLD-1, clan_public_keys).expect("wrong number of values");
    let tribe_public_key: PublicKey = tribe_public_key_g1.into();

    let rand_poly: Poly = Poly::random(TRIBE_THRESHOLD-1, &mut rng);
    let rand_public_key: PublicKeySet =  rand_poly.commitment().into();

    let tribe_signature = match rand_public_key.combine_signatures(clan_signatures.iter()) {
        Ok(sig) => sig,
        Err(e) => return Err(format_err!("Unexpected Error {:?}: Not able to generate Signature with THRESHOLD + 1 sig_shares", e)),
    };

    assert!(tribe_public_key.verify(&tribe_signature, msg));


    Ok(())
}



#[test]
fn having_min_unresponsive_nodes_cause_block() -> Result<()> {
    let mut rng = rand::thread_rng();


    // Assuming the first clan has threshold+1 unresponsive nodes
    let mut non_responsives = BTreeSet::<u64>::new();
    for i in 0..(NODES_PER_CLAN - CLAN_THRESHOLD) as u64 {
        let _ = non_responsives.insert(i);
    }


    let (peer_ids, mut generators) = setup_generators(&mut rng, non_responsives.clone())?;

    // The `messaging` function only ignores the non-initial proposals from a non-responsive node.
    // i.e. the Initialization phase will be completed and transits into Proposal.
    // With more non-responsive nodes, `finalize_contributing_phase` returns with Complaints of
    // non-contributors, and trigger the transition into Complaint phase. However, the Complaint
    // phase will be blocked as cannot collect more than threshold votes.
    // And the phase shall be blocked at Proposal.
    let mut proposals = Vec::new();

    // Trigger `finalize_contributing_phase` first, and exchange complaints
    peer_ids.iter().enumerate().for_each(|(index, _peer_id)| {
        if let Ok(proposal_vec) = generators[index].timed_phase_transition(&mut rng) {
            if !non_responsives.contains(&(index as u64)) {
                for proposal in proposal_vec {
                    proposals.push(proposal);
                }
            }
        }
    });
    messaging(
        &mut rng,
        &mut generators,
        &mut proposals,
        non_responsives.clone(),
    );

    // Then trigger `finalize_complaining_phase`, phase shall be blocked due to too many non-voters.
    for (index, peer_id) in peer_ids.iter().enumerate() {
        if let Err(err) = generators[index].timed_phase_transition(&mut rng) {
            assert_eq!(err, Error::TooManyNonVoters);
        } else {
            return Err(format_err!(
                "Node {:?}-{:?} shall not progress anymore",
                index,
                peer_id
            ));
        }
    }
    // List already returned within the above call to `finalize_complaining_phase`. So here it
    // returns an empty list.
    /*generators
        .iter()
        .for_each(|generator| assert!(generator.possible_blockers().is_empty()));*/
    Ok(())
}





/*


#[test]
fn threshold_signature() -> Result<()> {
    let mut rng = rand::thread_rng();
    let (_, generators) = setup_generators(&mut rng, BTreeSet::new())?;

    // Compute the keys and threshold signature shares.
    let msg = "Hello from the group!";

    let pub_key_set = generators[0]
        .generate_keys()
        .expect("Failed to generate `PublicKeySet` for node #0")
        .1
        .public_key_set;

    let mut sig_shares = BTreeMap::new();
    for (idx, generator) in generators.iter().enumerate() {
        assert!(generator.is_ready());
        let outcome = if let Some(outcome) = generator.generate_keys() {
            outcome.1
        } else {
            return Err(format_err!(
                "Failed to generate `PublicKeySet` and `SecretKeyShare` for node #{}",
                idx
            ));
        };
        let sk = outcome.secret_key_share;
        let pks = outcome.public_key_set;
        assert_eq!(pks, pub_key_set);
        let sig = sk.sign(msg);
        assert!(pks.public_key_share(idx).verify(&sig, msg));
        let _ = sig_shares.insert(idx, sig);
    }

    // Test threshold signature verification for a combination of signatures
    let sig_combinations = sig_shares.iter().combinations(THRESHOLD + 1);

    let deficient_sig_combinations = sig_shares.iter().combinations(THRESHOLD);

    for combination in deficient_sig_combinations.clone() {
        match pub_key_set.combine_signatures(combination) {
            Ok(_) => {
                return Err(format_err!(
                    "Unexpected Success: Signatures cannot be aggregated with THRESHOLD shares"
                ));
            }
            Err(e) => assert_eq!(format!("{:?}", e), "NotEnoughShares".to_string()),
        }
    }

    for combination in sig_combinations.clone() {
        let sig = pub_key_set
            .combine_signatures(combination)
            .expect("signature shares match");
        assert!(pub_key_set.public_key().verify(&sig, msg));
    }

    // Test signatures aggregated from a combination of different share - should be the same
    for signature_shares in sig_combinations.collect_vec().windows(2) {
        let sig = pub_key_set
            .combine_signatures(signature_shares[0].clone())
            .expect("signature shares match");
        let sig_ser = if let Ok(sig_ser) = serialize(&sig) {
            sig_ser
        } else {
            return Err(format_err!("cannot serialize signature 1"));
        };
        let sig2 = pub_key_set
            .combine_signatures(signature_shares[1].clone())
            .expect("signature shares match");
        let sig2_ser = if let Ok(sig_ser) = serialize(&sig2) {
            sig_ser
        } else {
            return Err(format_err!("cannot serialize signature 2"));
        };
        assert_eq!(sig_ser, sig2_ser);
    }
    Ok(())
}

#[test]
fn threshold_encrypt() -> Result<()> {
    let mut rng = rand::thread_rng();
    let (_, generators) = setup_generators(&mut rng, BTreeSet::new())?;

    // Compute the keys and decryption shares.
    let msg = "Help for threshold encryption unit test!".as_bytes();

    let pub_key_set = generators[0]
        .generate_keys()
        .expect("Failed to generate `PublicKeySet` for node #0")
        .1
        .public_key_set;
    let ciphertext = pub_key_set.public_key().encrypt(msg);

    let mut dec_shares = BTreeMap::new();

    for (idx, generator) in generators.iter().enumerate() {
        assert!(generator.is_ready());
        let outcome = if let Some(outcome) = generator.generate_keys() {
            outcome.1
        } else {
            return Err(format_err!(
                "Failed to generate `PublicKeySet` and `SecretKeyShare` for node #{}",
                idx
            ));
        };
        let sk = outcome.secret_key_share;
        let pks = outcome.public_key_set;
        assert_eq!(pks, pub_key_set);
        let dec_share = if let Some(dec_share) = sk.decrypt_share(&ciphertext) {
            dec_share
        } else {
            return Err(format_err!("Cannot create a decrypt share."));
        };
        assert!(pks
            .public_key_share(idx)
            .verify_decryption_share(&dec_share, &ciphertext));

        let _ = dec_shares.insert(idx, dec_share);
    }
    // Test threshold encryption verification for a combination of shares - should pass as there
    // are THRESHOLD + 1 shares aggregated in each combination
    let dec_share_combinations = dec_shares.iter().combinations(THRESHOLD + 1);
    for dec_share in dec_share_combinations {
        let decrypted = if let Ok(decrypted) = pub_key_set.decrypt(dec_share, &ciphertext) {
            decrypted
        } else {
            return Err(format_err!("Cannot verify a decrypt share."));
        };
        assert_eq!(msg, decrypted.as_slice());
    }

    // Test threshold decryption for a combination of shares - shouldn't decrypt as there
    // are THRESHOLD shares in each combination which are not enough to aggregate
    let deficient_dec_share_combinations = dec_shares.iter().combinations(THRESHOLD);
    for deficient_dec_share in deficient_dec_share_combinations {
        match pub_key_set.decrypt(deficient_dec_share, &ciphertext) {
            Ok(_) => {
                return Err(format_err!(
                    "Unexpected Success: Cannot decrypt by aggregating THRESHOLD shares"
                ))
            }
            Err(e) => assert_eq!(format!("{:?}", e), "NotEnoughShares".to_string()),
        }
    }
    Ok(())
}

#[test]
fn network_churning() -> Result<()> {
    let mut rng = rand::thread_rng();

    let initial_num = 3;
    let mut peer_ids = create_ids(initial_num);

    let mut naming_index = initial_num;

    while naming_index < 15 {
        if peer_ids.len() < NODENUM || rng.gen() {
            peer_ids.push(PeerId::new());
            naming_index += 1;
        } else {
            let _ = peer_ids.remove(rng.gen_range(0..peer_ids.len()));
        }

        let threshold: usize = peer_ids.len() * 2 / 3;
        let mut generators = create_generators(&mut rng, BTreeSet::new(), &peer_ids, threshold)?;

        assert!(generators
            .iter_mut()
            .all(|key_gen| key_gen.generate_keys().is_some()));
    }
    Ok(())
}
*/
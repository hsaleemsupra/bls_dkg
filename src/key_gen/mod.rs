// Copyright (c) 2022, MaidSafe.
// All rights reserved.
//
// This SAFE Network Software is licensed under the BSD-3-Clause license.
// Please see the LICENSE file for more details.

mod encryptor;
pub mod message;
pub mod outcome;
mod rng_adapter;

#[cfg(test)]
mod tests;


use bincode::{self, deserialize, serialize};
use blsttc::{group::{ff::Field, prime::PrimeCurveAffine}, poly::{Poly, BivariatePolynomial}, serde_impl::FieldWrap, Fr, G1Affine, G1};
pub use blsttc::{PublicKeySet, SecretKeyShare};
use encryptor::{Encryptor, Iv, Key};
use message::Message;
use outcome::Outcome;
use rand::{self, RngCore};
use serde_derive::{Deserialize, Serialize};
use std::collections::{btree_map::Entry};
use std::{
    fmt::{self, Debug, Formatter},
    mem,
    ops::{AddAssign, Mul},
};
use std::collections::btree_map::BTreeMap;
use std::collections::btree_set::BTreeSet;
use blsttc::blstrs::Scalar;
use blsttc::poly::Commitment;
use xor_name::XorName;

/// A local error while handling a message, that was not caused by that message being invalid.
#[non_exhaustive]
#[derive(Clone, Eq, thiserror::Error, PartialEq, Debug)]
pub enum Error {
    /// Unknown error.
    #[error("Unknown")]
    Unknown,
    /// Invalid threshold error.
    #[error("Invalid threshold")]
    InvalidThreshold,
    /// Unknown sender.
    #[error("Unknown sender")]
    UnknownSender,
    /// Failed to serialize message.
    #[error("Serialization error: {}", _0)]
    Serialization(String),
    /// Network error from Quic-P2P.
    #[error("QuicP2P error: {}", _0)]
    QuicP2P(String),
    /// Failed to encrypt message.
    #[error("Encryption error")]
    Encryption,
    /// Failed to finalize Complaint phase due to too many non-voters.
    #[error("Too many non-voters error")]
    TooManyNonVoters,
    /// Failed to reconstruct due to less points.
    #[error("Less than threshold+1 points for reconstruction")]
    ReconstructionError,
    /// Unexpected phase.
    #[error("Unexpected phase")]
    UnexpectedPhase { expected: Phase, actual: Phase },
    /// Ack on a missed part.
    #[error("ACK on missed part")]
    MissingPart,
}

impl From<Box<bincode::ErrorKind>> for Error {
    fn from(err: Box<bincode::ErrorKind>) -> Error {
        Error::Serialization(format!("{:?}", err))
    }
}

/// A contribution by a node for the key generation. The part shall only be handled by the receiver.
#[derive(Deserialize, Serialize, Clone, Hash, Eq, PartialEq)]
pub struct Part {
    // Index of the peer that expected to receive this Part.
    receiver: (u64, u64),
    // Our poly-commitment.
    commitment_pedersen: Commitment,
    // Our poly-commitment.
    commitment_feldman: Commitment,
    // point evaluation with f(x) for the receiver
    point_eval: Vec<u8>,
    // point evaluation with f'(x) for the receiver used in pedersen vss
    point_eval_prime: Vec<u8>,

}

impl Debug for Part {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Part")
            .field(&format!("<receiver {}, {}>", &self.receiver.0, &self.receiver.1))
            .field(&format!("<degree {}>", self.commitment_pedersen.degree()))
            //.field(&format!("<{} enc points size>", self.enc_points.len()))
            .finish()
    }
}


/// The information needed to track a single proposer's secret sharing process.
#[derive(Debug, PartialEq, Eq)]
struct ProposalState {
    /// The proposer's commitment.
    commitment_pedersen: Commitment,
    /// The proposer's commitment.
    commitment_feldman: Commitment,
    /// The share of f(x) we received
    value: Fr,
    /// The share of f'(x) we received
    value_prime: Fr,

}

impl ProposalState {
    /// Creates a new part state with a commitment.
    fn new(commitment_pedersen: Commitment) -> ProposalState {
        ProposalState {
            commitment_pedersen,
            commitment_feldman: Poly::zero().commitment(),
            value: Fr::zero(),
            value_prime: Fr::zero(),
        }
    }

}

impl<'a> serde::Deserialize<'a> for ProposalState {
    fn deserialize<D: serde::Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> {
        let (commitment_pedersen, commitment_feldman, value, value_prime) = serde::Deserialize::deserialize(deserializer)?;
        Ok(Self {
            commitment_pedersen,
            commitment_feldman,
            value,
            value_prime,
        })
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
pub enum Phase {

    //Phases for Pedersen-VSS
    Initialization,
    Contribution_Pedersen,
    Complaining_Pedersen,
    Justification_Pedersen,

    //Phases for Feldman-VSS
    Contribution_Feldman,
    Complaining_Feldman,
    Reconstruction_Feldman,
    Finalization_Feldman,


}

#[derive(Default)]
struct InitializationAccumulator {
    clans: usize,
    senders: BTreeSet<(u64,u64)>,
    initializations: BTreeMap<(u64, usize, usize, usize, usize, Vec<BTreeSet<XorName>>), usize>,
}

impl InitializationAccumulator {
    fn new(clans:usize) -> InitializationAccumulator {
        InitializationAccumulator {
            clans,
            senders: BTreeSet::new(),
            initializations: BTreeMap::new(),
        }
    }

    fn add_initialization(
        &mut self,
        // Following the `m of n` terminology, here m is the threshold and n is the total number.
        m1: usize,
        n1: usize,
        m2: usize,
        n2: usize,
        sender: (u64, u64),
        member_list: Vec<BTreeSet<XorName>>,
    ) -> Option<(u64, usize, usize, usize, usize, Vec<BTreeSet<XorName>>)> {

        if sender.0 as usize >= self.clans{
            return None;
        }

        if !self.senders.insert(sender) {
            return None;
        }

        let mut paras = (sender.0, m1, n1, m2, n2, member_list);
        let value = self.initializations.entry(paras.clone()).or_insert(0);
        *value += 1;

        //check of threshold number of clans have correct tribe configuration
        let mut total_valid_clans = 0;

        for i in 0..self.clans{
            paras.0 = i as u64;
            let value = self.initializations.entry(paras.clone()).or_insert(0);
            if *value >= m2 {
                total_valid_clans = total_valid_clans + 1;
            }
        }

        if total_valid_clans >= m1{
            Some(paras)
        }
        else{
            None
        }

    }
}

#[derive(Default)]
struct ComplaintsAccumulatorPedersen {
    names: BTreeSet<XorName>,
    // Indexed by complaining targets.
    complaints: BTreeMap<XorName, BTreeSet<XorName>>,
}

impl ComplaintsAccumulatorPedersen {
    fn new(tribe: Vec<BTreeSet<XorName>>) -> ComplaintsAccumulatorPedersen {

        let mut names = BTreeSet::new();

        for i in 0..tribe.len() {
            let clan: Vec<_> = tribe[i].iter().cloned().collect();
            for j in 0..clan.len(){
                names.insert(clan[j]);
            }
        }


        ComplaintsAccumulatorPedersen {
            names,
            complaints: BTreeMap::new(),
        }
    }

    // TODO: accusation shall be validated.
    fn add_complaint(&mut self, sender_id: XorName, target_id: XorName, _msg: Vec<u8>) {
        if !self.names.contains(&sender_id) || !self.names.contains(&target_id) {
            return;
        }

        match self.complaints.entry(target_id) {
            Entry::Occupied(mut entry) => {
                let _ = entry.get_mut().insert(sender_id);
            }
            Entry::Vacant(entry) => {
                let mut targets = BTreeSet::new();
                let _ = targets.insert(sender_id);
                let _ = entry.insert(targets);
            }
        }
    }

}

#[derive(Default)]
struct ComplaintsAccumulatorFeldman {
    complaints: BTreeMap<XorName, BTreeMap< (u64, u64), Vec<u8> >>,
}

impl ComplaintsAccumulatorFeldman {
    fn new() -> ComplaintsAccumulatorFeldman {
        ComplaintsAccumulatorFeldman {
            complaints: BTreeMap::new(),
        }
    }

}




pub type MessageAndTarget = (XorName, Message);

/// An algorithm for dealerless distributed key generation.
///
/// This is trying to follow the protocol as suggested at
/// <https://github.com/dashpay/dips/blob/master/dip-0006/bls_m-of-n_threshold_scheme_and_dkg.md#distributed-key-generation-dkg-protocol>
///
/// A normal usage flow will be:
///
/// 1. Call [`initialize`](Self::initialize) first to generate an instance.
/// 2. Multicasting the return [`Message`] to all participants.
/// 3. Call [`handle_message`](Self::handle_message) function to handle the incoming `Message` and
///    multicasting the resulting `Message`s (if any) to all participants.
/// 4. Call [`timed_phase_transition`](Self::timed_phase_transition) to complete the complaining
///    phase.
/// 5. Repeat step 3 when there is incoming `Message`.
/// 6. Call [`generate_keys`](Self::generate_keys) to get the public-key set and secret-key share,
///    if the procedure finalized.
pub struct KeyGen {
    /// Our node ID.
    our_id: XorName,
    /// Our node index in a clan.
    our_index: (u64, u64),
    /// Our proposed Bivariate Polynomial
    our_part: BivariatePolynomial,
    /// Our Bivariate Polynomial used for Pedersen Commitment
    our_part_pedersen: BivariatePolynomial,
    /// The names of all nodes, by node ID.
    tribe: Vec<BTreeSet<XorName>>,
    /// Alternate representation of tribe for lookup efficiency
    names: BTreeMap<XorName, (u64, u64)>,
    /// Total members in the tribe
    total_members: usize,
    /// Carry out encryption work during the DKG process.
    //encryptor: Encryptor,
    /// Proposed bivariate polynomials.
    parts: BTreeMap<(u64, u64), ProposalState>,
    /// Maximum number of corrupt clans in a tribe
    /// (tribe_threshold + 1) shares required to reconstruct the secret
    /// Polynomial x degree = tribe_threshold
    tribe_threshold: usize,
    /// parameter for pedersen commitments
    h: G1,
    /// Maximum number of corrupt nodes in a clan
    /// (clan_threshold + 1) shares required to reconstruct the secret
    /// Polynomial y degree = clan_threshold
    clan_threshold: usize,
    /// set of disqualified nodes
    disqual_set: BTreeSet<XorName>,
    /// Current DKG phase.
    phase: Phase,
    /// Accumulates initializations.
    initalization_accumulator: InitializationAccumulator,
    /// Accumulates complaints.
    complaints_accumulator: ComplaintsAccumulatorPedersen,
    /// Accumulates complaints for Feldman VSS.
    complaints_accumulator_feldman: ComplaintsAccumulatorFeldman,
    /// Pending complain messages.
    pending_complain_messages: Vec<Message>,
    /// Cached messages to be used for reply unhandable.
    message_cache: BTreeMap<XorName, Message>,
}

impl KeyGen {
    /// Creates a new `KeyGen` instance, together with the `Initial` message that should be
    /// multicast to all nodes.
    pub fn initialize(
                      our_id: XorName,
                      total_clans: usize,
                      tribe_threshold: usize,
                      members_per_clan: usize,
                      clan_threshold: usize,
                      tribe: Vec<BTreeSet<XorName>>,
                      h: G1,
    ) -> Result<(KeyGen, Vec<MessageAndTarget>), Error> {

        if tribe.len() < tribe_threshold {
            return Err(Error::Unknown);
        }

        for clan in &tribe{
            if (*clan).len()<clan_threshold{
                return Err(Error::Unknown);
            }
        }

        let mut clan_index: i32  = -1;
        let mut member_index: i32  = -1;
        let mut total_mem :usize = 0;

        let mut names: BTreeMap<XorName, (u64,u64)> = BTreeMap::new();

        for i in 0..tribe.len() {
            let clan: Vec<_> = tribe[i].iter().cloned().collect();
            for j in 0..clan.len(){
               names.insert(clan[j], (i as u64, j as u64));
            }
        }

        for i in 0..tribe.len() {
            let clan: Vec<_> = tribe[i].iter().cloned().collect();
            for j in 0..clan.len(){
                total_mem = total_mem+1;

                if clan[j] == our_id{
                    clan_index = i as i32;
                    member_index = j as i32;
                }
            }
        }

        if clan_index == -1 || member_index == -1 {
            return Err(Error::Unknown);
        }

        let key_gen = KeyGen {
            our_id,
            our_index: ((clan_index) as u64, (member_index) as u64),
            our_part: BivariatePolynomial::zero(),
            our_part_pedersen: BivariatePolynomial::zero(),
            tribe: tribe.clone(),
            names: names.clone(),
            total_members: total_mem,
            //encryptor: Encryptor::new(&tribe),
            parts: BTreeMap::new(),
            tribe_threshold,
            h,
            clan_threshold,
            disqual_set: BTreeSet::new(),
            phase: Phase::Initialization,
            initalization_accumulator: InitializationAccumulator::new(total_clans),
            complaints_accumulator: ComplaintsAccumulatorPedersen::new(tribe.clone()),
            complaints_accumulator_feldman: ComplaintsAccumulatorFeldman::new(),
            pending_complain_messages: Vec::new(),
            message_cache: BTreeMap::new(),
        };

        let msg = Message::Initialization {
            key_gen_id: ((clan_index) as u64, (member_index) as u64),
            m1: tribe_threshold,
            n1: total_clans,
            m2: clan_threshold,
            n2: members_per_clan,
            member_list: tribe.clone(),
        };

        let mut messages: Vec<MessageAndTarget> = vec![];
        for x in tribe {
            for y in x {
                messages.push((y, msg.clone()));
            }
        }

        Ok((key_gen, messages))
    }

    pub fn phase(&self) -> Phase {
        self.phase
    }

    /// Dispatching an incoming dkg message.
    pub fn handle_message<R: RngCore>(
        &mut self,
        rng: &mut R,
        msg: Message,
    ) -> Result<Vec<MessageAndTarget>, Error> {
        if self.is_finalized() {
            return Ok(Vec::new());
        }

        self.process_message(rng, msg)
    }

    /// Cached message will be returned as a list,
    /// with Initialization messages on top and Proposal behind.
    /// They shall get handled in such order on receiver side as well.
    pub fn get_cached_message(&self) -> Vec<Message> {
        let mut result = Vec::new();
        result.extend(
            self.message_cache
                .iter()
                .filter_map(|(_, msg)| match msg {
                    Message::Initialization { .. } => Some(msg.clone()),
                    _ => None,
                })
                .collect::<Vec<Message>>(),
        );
        result.extend(
            self.message_cache
                .iter()
                .filter_map(|(_, msg)| match msg {
                    Message::Proposal { .. } => Some(msg.clone()),
                    _ => None,
                })
                .collect::<Vec<Message>>(),
        );
        result
    }

    /// Handle upper layer cached messages even before this DKG session got started.
    /// Returns with messages need to be broadcast to all,
    /// AND unhandable messages need to be sent to the creator.
    /// It is also being used when handle message_history due to unhandable.
    pub fn handle_pre_session_messages<R: RngCore>(
        &mut self,
        rng: &mut R,
        mut cache_messages: Vec<Message>,
    ) -> (Vec<MessageAndTarget>, Vec<MessageAndTarget>) {
        let mut msgs = Vec::new();
        let mut updated = false;
        loop {
            trace!("new round polling history messages");
            let pending_messages = std::mem::take(&mut cache_messages);
            for message in pending_messages {
                if let Ok(new_messages) = self.process_message(rng, message.clone()) {
                    if self.is_finalized() {
                        return (Vec::new(), Vec::new());
                    }
                    msgs.extend(new_messages);
                    updated = true;
                } else {
                    trace!("pushing back history message {:?}", message);
                    cache_messages.push(message);
                }
            }
            if !updated {
                break;
            } else {
                updated = false;
            }
        }

        let mut unhandables = Vec::new();
        for msg in cache_messages {
            let sender = if let Some(name) = self.node_id_from_index(msg.creator()) {
                name
            } else {
                warn!(
                    "cannot get name of index {:?} among {:?}",
                    msg.creator(),
                    self.tribe
                );
                continue;
            };
            unhandables.push((sender, msg));
        }
        (msgs, unhandables)
    }

    fn process_message<R: RngCore>(
        &mut self,
        rng: &mut R,
        msg: Message,
    ) -> Result<Vec<MessageAndTarget>, Error> {
        trace!(
            "{:?} with phase {:?} handle DKG message {:?}-{:?}",
            self,
            self.phase,
            msg.id(),
            msg
        );
        let result = match msg.clone() {
            Message::Initialization {
                key_gen_id,
                m1,
                n1,
                m2,
                n2,
                member_list,
            } => {
                let _ = self.message_cache.insert(msg.id(), msg);
                self.handle_initialization(rng, m1, n1, m2, n2,  key_gen_id, member_list)
            }
            Message::Proposal { key_gen_id, part } => self.handle_proposal_pedersen(key_gen_id, part),
            Message::Complaint {
                key_gen_id,
                target,
                msg,
            } => self.handle_complaint_pedersen(key_gen_id, target, msg),
            Message::Justification {
                key_gen_id,
                contribution,
            } => self.handle_justification(key_gen_id, contribution),
            Message::Proposal_Feldman { key_gen_id, part} => self.handle_proposal_feldman(key_gen_id, part),
            Message::Complaint_Feldman {
                key_gen_id,
                target,
                point_eval,
                point_eval_prime} =>self.handle_complaint_feldman(key_gen_id, target, point_eval, point_eval_prime),

            Message::Reconstruction {
                key_gen_id,
                complained_node,
                point_eval
            }  => self.handle_reconstruction(key_gen_id, complained_node, point_eval),



        };
        self.multicasting_messages(result?)
    }

    // Handles an incoming initialize message. Creates the `Proposal` message once quorum
    // agreement reached, and the message should be multicast to all nodes.
    fn handle_initialization<R: RngCore>(
        &mut self,
        rng: &mut R,
        m1: usize,
        n1: usize,
        m2: usize,
        n2: usize,
        sender: (u64, u64),
        member_list: Vec<BTreeSet<XorName>>,
    ) -> Result<Vec<Message>, Error> {
        if self.phase != Phase::Initialization {
            return Ok(Vec::new());
        }

        if let Some((_sender_clan, m1, _n1, m2, _n2,  member_list)) =
            self.initalization_accumulator
                .add_initialization(m1, n1, m2, n2, sender, member_list)
        {

            self.tribe_threshold = m1;
            self.clan_threshold = m2;
            self.tribe = member_list;

            //self.init_names(&mut self.names, &self.tribe);
            self.names.clear();
            for i in 0..self.tribe.len() {
                let clan: Vec<_> = self.tribe[i].iter().cloned().collect();
                for j in 0..clan.len(){
                    self.names.insert(clan[j], (i as u64, j as u64));
                }
            }


            self.total_members = self.names.len();

            self.phase = Phase::Contribution_Pedersen;

            let mut rng = rng_adapter::RngAdapter(&mut *rng);
            self.our_part = BivariatePolynomial::random(m1, m2, &mut rng);
            self.our_part_pedersen = BivariatePolynomial::random(m1, m2, &mut rng);


            let mut result: Vec<Message> = Vec::new();

            for i in 0..self.tribe.len() {

                let univar_poly = self.our_part.get_univariate_poly( i+1);
                let univar_poly_prime = self.our_part_pedersen.get_univariate_poly( i+1);

                let univar_commitment_pedersen = univar_poly.pedersen_commitment(&univar_poly_prime, self.h);

                let mut values = Vec::new();
                let mut values_prime = Vec::new();

                let clan: Vec<_> = self.tribe[i].iter().cloned().collect();
                for j in 0..clan.len(){
                    let eval = univar_poly.evaluate(j+1);
                    let eval_prime = univar_poly_prime.evaluate(j+1);

                    let ser_val = serialize(&FieldWrap(eval))?;
                    let ser_val_prime = serialize(&FieldWrap(eval_prime))?;

                    values.push(ser_val);
                    values_prime.push(ser_val_prime);
                }

                for j in 0..clan.len(){
                    result.push(
                        Message::Proposal {
                            key_gen_id: self.our_index,
                            part: Part {
                                receiver: (i as u64, j as u64),
                                commitment_pedersen: univar_commitment_pedersen.clone(),
                                commitment_feldman: Poly::zero().commitment(),
                                point_eval: values[j].clone(),
                                point_eval_prime: values_prime[j].clone(),
                            }
                        })
                }

            }

            return Ok(result);

        }
        Ok(Vec::new())
    }

    // Handles a `Proposal` message during the Pedersen-VSS `Contribution` phase.
    // When there is an invalidation happens, holds the `Complaint` message till broadcast out
    // when `finalize_contributing` being called.
    fn handle_proposal_pedersen(&mut self, sender_index: (u64, u64), part: Part) -> Result<Vec<Message>, Error> {
        if self.phase == Phase::Initialization {
            return Err(Error::UnexpectedPhase {
                expected: Phase::Contribution_Pedersen,
                actual: self.phase,
            });
        } else if !(self.phase == Phase::Contribution_Pedersen) {
            return Ok(Vec::new());
        }

        let _point_eval = match self.handle_part_or_fault(sender_index, part.clone()) {
            Ok(Some(_point_eval)) => return Ok(Vec::new()),
            Ok(None) => return Ok(Vec::new()),
            Err(_fault) => {
                let msg = Message::Proposal {
                    key_gen_id: sender_index,
                    part,
                };
                debug!(
                    "{:?} complain {:?} with Error {:?} when handling a proposal",
                    self, sender_index, _fault
                );
                let invalid_contribute = serialize(&msg)?;
                self.pending_complain_messages.push(Message::Complaint {
                    key_gen_id: self.our_index,
                    target: sender_index,
                    msg: invalid_contribute,
                });
                return Ok(Vec::new());
            }
        };


    }

    // Handles a `Proposal` message during the Feldman `Contribution` phase.
    // When there is an invalidation happens, holds the `Complaint` message till broadcast out
    // when `finalize_contributing` being called.=
    fn handle_proposal_feldman(&mut self, sender_index: (u64, u64), part: Part) -> Result<Vec<Message>, Error> {
        if self.phase == Phase::Justification_Pedersen {
            return Err(Error::UnexpectedPhase {
                expected: Phase::Contribution_Feldman,
                actual: self.phase,
            });
        } else if !(self.phase == Phase::Contribution_Feldman) {
            return Ok(Vec::new());
        }

        let _point_eval = match self.handle_part_or_fault_feldman(sender_index, part.clone()) {
            Ok(Some(_point_eval)) => return Ok(Vec::new()),
            Ok(None) => return Ok(Vec::new()),
            Err(_fault) => {
                debug!(
                    "{:?} complain {:?} with Error {:?} when handling a proposal",
                    self, sender_index, _fault
                );

                let proposal = self.parts.get(&sender_index).unwrap();
                let ser_val = serialize(&FieldWrap(proposal.value))?;
                let ser_val_prime = serialize(&FieldWrap(proposal.value_prime))?;

                self.pending_complain_messages.push(Message::Complaint_Feldman {
                    key_gen_id: self.our_index,
                    target: sender_index,
                    point_eval: ser_val,
                    point_eval_prime: ser_val_prime,
                });
                return Ok(Vec::new());
            }
        };


    }

    fn handle_reconstruction(&mut self, sender_index: (u64, u64), complained_node: XorName, point_eval: Vec<u8>) -> Result<Vec<Message>, Error>{

        if !(self.phase == Phase::Reconstruction_Feldman) {
            return Ok(Vec::new());
        }

        if !(sender_index.0 == self.our_index.0){
            return Ok(Vec::new());
        }


        let sender_id = self.node_id_from_index(sender_index).unwrap();
        if self.disqual_set.contains(&sender_id){
            return Ok(Vec::new());

        }

        if self.complaints_accumulator_feldman.complaints.contains_key(&complained_node){

            let entry = self.complaints_accumulator_feldman.complaints.get_mut(&complained_node).unwrap();
            entry.insert(sender_index,point_eval);

        }

        Ok(Vec::new())

    }


    pub fn all_contribution_received(&self) -> bool {
        self.total_members == self.parts.len()
    }

    fn finalize_contributing_phase_pedersen(&mut self) -> Vec<Message> {
        self.phase = Phase::Complaining_Pedersen;

        for non_contributor in self.non_contributors_pedersen().0 {
            debug!(
                "{:?} complain {:?} for non-contribution during Contribution phase",
                self, non_contributor
            );
            self.pending_complain_messages.push(Message::Complaint {
                key_gen_id: self.our_index,
                target: non_contributor,
                msg: b"Not contributed".to_vec(),
            });
        }
        debug!(
            "{:?} has {:?} complain message and is {:?} ready",
            self,
            self.pending_complain_messages.len(),
            self.is_ready()
        );
        // In case of ready, transit into `Finalization` phase.
        /*if self.is_ready() {
            self.become_finalization();
        }*/

        mem::take(&mut self.pending_complain_messages)
    }

    fn finalize_contributing_phase_feldman(&mut self) -> Vec<Message> {
        self.phase = Phase::Complaining_Feldman;

        //add non-contributers to the complaints set
        for noncontributer in self.non_contributors_feldman().1{
            self.complaints_accumulator_feldman.complaints.insert(noncontributer,BTreeMap::new());

        }

        Vec::new()
    }

    fn non_contributors_pedersen(&self) -> (BTreeSet<(u64, u64)>, BTreeSet<XorName>) {
        let mut non_idxes = BTreeSet::new();
        let mut non_ids = BTreeSet::new();

        for i in 0..self.tribe.len() {
            let clan: Vec<_> = self.tribe[i].iter().cloned().collect();
            for j in 0..clan.len(){

                if let Some(_proposal_sate) = self.parts.get(&( i as u64, j as u64) ) {

                }

                else {
                    let _ = non_idxes.insert((i as u64, j as u64));
                    let _ = non_ids.insert(clan[j]);
                }

            }
        }


        (non_idxes, non_ids)
    }

    fn non_contributors_feldman(&self) -> (BTreeSet<(u64, u64)>, BTreeSet<XorName>) {
        let mut non_idxes = BTreeSet::new();
        let mut non_ids = BTreeSet::new();

        for i in 0..self.tribe.len() {
            let clan: Vec<_> = self.tribe[i].iter().cloned().collect();
            for j in 0..clan.len(){

                if !self.disqual_set.contains(&clan[j]){

                    let contribution = self.parts.get(&(i as u64,j as u64)).unwrap();
                    if contribution.commitment_feldman == Poly::zero().commitment(){

                        let _ = non_idxes.insert((i as u64, j as u64));
                        let _ = non_ids.insert(clan[j]);

                    }
                }


            }
        }


        (non_idxes, non_ids)
    }


    // TODO: So far this function has to be called externally to indicates a completion of the
    //       contribution phase. That is, the owner of the key_gen instance has to wait for a fixed
    //       interval, say an expected timer of 5 minutes, to allow the messages to be exchanged.
    //       May need to be further verified whether there is a better approach.
    pub fn timed_phase_transition<R: RngCore>(
        &mut self,
        rng: &mut R,
    ) -> Result<Vec<MessageAndTarget>, Error> {
        trace!("{:?} current phase is {:?}", self, self.phase);
        let result = match self.phase {
            Phase::Contribution_Pedersen => Ok(self.finalize_contributing_phase_pedersen()),
            Phase::Complaining_Pedersen => self.finalize_complaining_phase_pedersen(rng),
            Phase::Justification_Pedersen => self.finalize_justification_phase(),
            Phase::Contribution_Feldman => Ok(self.finalize_contributing_phase_feldman()),
            Phase::Complaining_Feldman => self.finalize_complaining_phase_feldman(),
            Phase::Reconstruction_Feldman => self.finalize_reconstruction_phase(),
            Phase::Finalization_Feldman => Ok(Vec::new()),
            Phase::Initialization => Err(Error::UnexpectedPhase {
                expected: Phase::Contribution_Pedersen,
                actual: self.phase,
            }),

        };
        self.multicasting_messages(result?)
    }

    // Specify the receiver of the DKG messages explicitly
    // to avoid un-necessary broadcasting.
    fn multicasting_messages(
        &mut self,
        messages: Vec<Message>,
    ) -> Result<Vec<MessageAndTarget>, Error> {
        let mut messaging = Vec::new();
        for message in messages {
            match message {
                Message::Proposal { ref part, .. } => {
                    // Proposal to us cannot be used by other.
                    // So the cache must be carried out on sender side.
                    let _ = self.message_cache.insert(message.id(), message.clone());

                    let receiver = if let Some(name) = self.node_id_from_index(part.receiver) {
                        name
                    } else {
                        warn!(
                            "For a Proposal, Cannot get name of index {:?} among {:?}",
                            part.receiver, self.tribe
                        );
                        continue;
                    };
                    messaging.push((receiver, message));
                }

                Message::Proposal_Feldman { ref part, .. } => {
                    // Proposal to us cannot be used by other.
                    // So the cache must be carried out on sender side.
                    let _ = self.message_cache.insert(message.id(), message.clone());

                    let receiver = if let Some(name) = self.node_id_from_index(part.receiver) {
                        name
                    } else {
                        warn!(
                            "For a Proposal, Cannot get name of index {:?} among {:?}",
                            part.receiver, self.tribe
                        );
                        continue;
                    };
                    messaging.push((receiver, message));
                }

                _ => {

                    for i in 0..self.tribe.len() {
                        let clan: Vec<_> = self.tribe[i].iter().cloned().collect();
                        for j in 0..clan.len(){
                            messaging.push((clan[j], message.clone()));
                        }
                    }
                }
            }
        }
        Ok(messaging)
    }

    // Handles a `Complaint` message.
    fn handle_complaint_pedersen(
        &mut self,
        sender_index: (u64, u64),
        target_index: (u64, u64),
        invalid_msg: Vec<u8>,
    ) -> Result<Vec<Message>, Error> {
        if self.phase != Phase::Complaining_Pedersen {
            trace!("To avoid triggering AE pattern, skip this so far");
            return Ok(Vec::new());
        }

        let sender_id = self
            .node_id_from_index(sender_index)
            .ok_or(Error::UnknownSender)?;
        let target_id = self
            .node_id_from_index(target_index)
            .ok_or(Error::Unknown)?;

        self.complaints_accumulator
            .add_complaint(sender_id, target_id, invalid_msg);
        Ok(Vec::new())
    }

    // Handles a `Complaint` message.
    fn handle_complaint_feldman(
        &mut self,
        sender_index: (u64, u64),
        target_index: (u64, u64),
        point_eval: Vec<u8>,
        point_eval_prime: Vec<u8>,
    ) -> Result<Vec<Message>, Error> {
        if self.phase != Phase::Complaining_Feldman {
            trace!("To avoid triggering AE pattern, skip this so far");
            return Ok(Vec::new());
        }

        let sender_id = self
            .node_id_from_index(sender_index)
            .ok_or(Error::UnknownSender)?;
        let target_id = self
            .node_id_from_index(target_index)
            .ok_or(Error::Unknown)?;


        if self.disqual_set.contains(&sender_id) || self.disqual_set.contains(&target_id){
            return Ok(Vec::new());
        }


        //We can only validate the complaint if it is from a sender from our clan
        if sender_index.0 != self.our_index.0{
            return Ok(Vec::new());
        }

        //We need to have the commitment stored to validate the complaint
        if self.parts.get(&target_index).unwrap().commitment_feldman == Poly::zero().commitment(){
            return Ok(Vec::new());
        }


        let val = deserialize::<FieldWrap<Fr>>(&point_eval)
            .map_err(|_| Error::Unknown)?
            .into_inner();

        let val_prime = deserialize::<FieldWrap<Fr>>(&point_eval_prime)
            .map_err(|_| Error::Unknown)?
            .into_inner();


        //verify complaint is valid
        if self.parts.get(&target_index).unwrap().commitment_pedersen.evaluate(sender_index.1 + 1)
            == (G1Affine::generator().mul(val) + self.h.mul(val_prime))
        {
            if self.parts.get(&target_index).unwrap().commitment_feldman.evaluate(sender_index.1 + 1)
                != G1Affine::generator().mul(val){

                self.complaints_accumulator_feldman.complaints.insert(target_id,BTreeMap::new());

            }

        }

        Ok(Vec::new())
    }

    fn finalize_complaining_phase_pedersen<R: RngCore>(
        &mut self,
        _rng: &mut R,
    ) -> Result<Vec<Message>, Error> {

        self.phase = Phase::Justification_Pedersen;

        // Remove the parties for which we received >clan_threshold complaints from any clan
        let failings = self.complaints_accumulator.complaints.clone();

        for failing in failings{
            let mut clan_complaints_count: Vec<u64> = vec![0;self.tribe.len()];

            for accuser in failing.1{

                let accuser_clan_idx = self.node_index(&accuser).unwrap().0 as usize;
                clan_complaints_count[accuser_clan_idx] = clan_complaints_count[accuser_clan_idx] + 1;

                if clan_complaints_count[accuser_clan_idx] > self.clan_threshold as u64 {

                    self.disqual_set.insert(failing.0);
                    self.complaints_accumulator.complaints.remove(&failing.0);
                    break;
                }

            }

        }

        if !self.is_ready(){
            return Err(Error::TooManyNonVoters);
        }


        let mut result = Vec::new();
        let failings = &self.complaints_accumulator.complaints;

        // Sending out a Justification message if find self is failed.
        if failings.contains_key(&self.our_id) {

            let accusers = failings.get(&self.our_id).unwrap();
            let mut contribution = BTreeMap::new();

            for accuser in accusers.iter(){
                let accuser_index = self.node_index(accuser).unwrap();
                let univar_poly = self.our_part.get_univariate_poly( accuser_index.0 + 1);
                let univar_poly_prime = self.our_part_pedersen.get_univariate_poly( accuser_index.0 + 1);
                let univar_commitment_pedersen = univar_poly.pedersen_commitment(&univar_poly_prime, self.h);


                let eval = univar_poly.evaluate(accuser_index.1 + 1);
                let eval_prime = univar_poly_prime.evaluate(accuser_index.1 + 1);


                let ser_val = serialize(&FieldWrap(eval))?;
                let ser_val_prime = serialize(&FieldWrap(eval_prime))?;

                contribution.insert(*accuser, (ser_val, ser_val_prime, univar_commitment_pedersen));

            }

            result.push(Message::Justification {
                key_gen_id: self.our_index,
                contribution: contribution,
            });

        }

        if failings.is_empty() && self.is_ready() {

            let res = self.handle_finalization_pedersen();
            return res;

        }

        Ok(result)
    }

    fn finalize_complaining_phase_feldman(
        &mut self,

    ) -> Result<Vec<Message>, Error> {


        // if no complaints ready to generate keys
        if self.complaints_accumulator_feldman.complaints.is_empty() {
            self.phase = Phase::Finalization_Feldman;
            return Ok(Vec::new());

        }



        //in case of complaints start pedersen-vss reconstruction phase
        self.phase = Phase::Reconstruction_Feldman;
        let mut result: Vec<Message> = Vec::new();


        for complaint in self.complaints_accumulator_feldman.complaints.clone() {

            let complaint_idx = self.node_index(&complaint.0).unwrap();
            let point_eval = self.parts.get(complaint_idx).unwrap().value;
            let ser_val = serialize(&FieldWrap(point_eval))?;

            result.push(
                Message::Reconstruction {
                    key_gen_id: self.our_index,
                    complained_node: complaint.0,
                    point_eval: ser_val.clone(),
                })

        }


        Ok(result)
    }


    fn finalize_justification_phase(&mut self) -> Result<Vec<Message>, Error> {

        //If there are pending complaints against a node, remove it from the Quals set
        let failings = self.complaints_accumulator.complaints.clone();

        for failing in failings{
            self.disqual_set.insert(failing.0);
        }


        if self.is_ready() {
            let res = self.handle_finalization_pedersen();
            return res;

        }
        else {
            return Err(Error::TooManyNonVoters);

        }

    }

    fn finalize_reconstruction_phase(&mut self) -> Result<Vec<Message>, Error> {


        for complaint in self.complaints_accumulator_feldman.complaints.clone(){

           let mut eval_pts = Vec::new();

           for i in 0..self.tribe.len(){

               let clan: Vec<_> = self.tribe[i].iter().cloned().collect();
               for j in 0..clan.len(){

                   if complaint.1.contains_key(&(i as u64, j as u64)){

                       let pt = complaint.1.get(&(i as u64, j as u64)).unwrap();

                       let val = deserialize::<FieldWrap<Fr>>(&pt )
                           .map_err(|_| Error::Unknown)?
                           .into_inner();

                       eval_pts.push(((j+1) as u64, val));

                       // we have enough points for reconstruction
                       if eval_pts.len() == self.clan_threshold + 1 {
                           break;
                       }

                   }

               }

           }

            // not enough points for reconstruction
            if eval_pts.len() < self.clan_threshold + 1{
                return Err(Error::ReconstructionError);

            }

            else{

                //set our commitment to interpolated polynomial
                let interpolated_poly = Poly::interpolate(eval_pts).unwrap();
                let complaint_index = self.node_index(&complaint.0).unwrap().clone();


                let part = self
                    .parts
                    .get_mut(&complaint_index)
                    .ok_or(Error::Unknown)?;


                part.commitment_feldman = interpolated_poly.commitment();

            }

        }


        self.phase = Phase::Finalization_Feldman;

        Ok(Vec::new())

    }


    // Handles a `Justification` message.
    fn handle_justification(
        &mut self,
        sender_index: (u64, u64),
        contribution: BTreeMap<XorName, (Vec<u8>, Vec<u8>, Commitment)>,
    ) -> Result<Vec<Message>, Error> {

        let sender_id = self.node_id_from_index(sender_index).unwrap();

        if self.complaints_accumulator.complaints.contains_key(&sender_id){

            let accusers = self.complaints_accumulator.complaints.get(&sender_id).unwrap();
            for accuser in accusers.iter(){

                // If the sender has not sent justification for any accuser return
                if !contribution.contains_key(accuser) {
                    self.disqual_set.insert(sender_id);
                    return Err(Error::Unknown);
                }
                else {
                    // Verify all justifications are correct
                    let accuser_contribution = contribution.get(accuser).unwrap();
                    let accuser_index = self.node_index(accuser).unwrap();
                    let val = deserialize::<FieldWrap<Fr>>(&(*accuser_contribution).0 )
                        .map_err(|_| Error::Unknown)?
                        .into_inner();

                    let val_prime = deserialize::<FieldWrap<Fr>>(&(*accuser_contribution).1 )
                        .map_err(|_| Error::Unknown)?
                        .into_inner();

                    if (*accuser_contribution).2.evaluate(accuser_index.1 + 1)
                        != (G1Affine::generator().mul(val) + self.h.mul(val_prime))
                    {
                        self.disqual_set.insert(sender_id);
                        return Err(Error::Unknown);
                    }

                    // In case the justification is intended for us
                    if self.our_index == *(accuser_index) {

                        // We already handled this `Part` before.
                        if let Some(state) = self.parts.get(&sender_index) {
                            if state.commitment_pedersen != (*accuser_contribution).2 {
                                return Err(Error::Unknown);
                            }

                        }
                        else {
                            let _ = self
                                .parts
                                .insert(sender_index, ProposalState::new((*accuser_contribution).2.clone()));

                            let part = self
                                .parts
                                .get_mut(&sender_index)
                                .ok_or(Error::Unknown)?;

                            let _ = part.value = val;
                            let _ = part.value_prime = val_prime;
                        }

                    }

                }

            }

            self.complaints_accumulator.complaints.remove(&sender_id);

        }

        return Ok(Vec::new());

    }

    fn handle_finalization_pedersen(&mut self) -> Result<Vec<Message>, Error> {
        self.pending_complain_messages.clear();
        self.phase = Phase::Contribution_Feldman;

        let mut result: Vec<Message> = Vec::new();

        for i in 0..self.tribe.len() {
            let univar_poly = self.our_part.get_univariate_poly( i+1);
            let univar_commitment = univar_poly.commitment();
            let clan: Vec<_> = self.tribe[i].iter().cloned().collect();

            for j in 0..clan.len(){

                let receiver_id = self.node_id_from_index((i as u64, j as u64) ).unwrap();
                if !self.disqual_set.contains(&receiver_id){
                    result.push(
                        Message::Proposal_Feldman {
                            key_gen_id: self.our_index,
                            part: Part {
                                receiver: (i as u64, j as u64),
                                commitment_pedersen: Poly::zero().commitment(),
                                commitment_feldman: univar_commitment.clone(),
                                point_eval: Vec::new(),
                                point_eval_prime: Vec::new()
                            }
                        })
                }
            }

        }

        return Ok(result);

    }


    /// Returns the index of the node, or `None` if it is unknown.
    fn node_index(&self, node_id: &XorName) -> Option<&(u64, u64)> {
        self.names.get(node_id)
    }

    /// Returns the id of the index, or `None` if it is unknown.
    pub fn node_id_from_index(&self, node_index: (u64, u64)) -> Option<XorName> {

        if node_index.0 < self.tribe.len() as u64{
            let clan: Vec<_> = self.tribe[node_index.0 as usize].iter().cloned().collect();

            if node_index.1 < clan.len() as u64 {
                return Some(clan[node_index.1 as usize]);
            }

        }

        None
    }

    // Returns `true` if in each clan we have at least >clan_threshold nodes in Qual set
    // So that we can safely generate the key later
    fn is_ready(&self) -> bool {

        let mut clan_complaints_count: Vec<u64> = vec![0;self.tribe.len()];

        for failing in self.disqual_set.clone(){

            let failed_clan_idx = self.node_index(&failing).unwrap().0 as usize;
            clan_complaints_count[failed_clan_idx] = clan_complaints_count[failed_clan_idx] + 1;

            if clan_complaints_count[failed_clan_idx] > self.clan_threshold as u64 {
                return false;
            }

        }

        return true;
    }

    /// Returns `true` if in the phase of Finalization.
    pub fn is_finalized(&self) -> bool {
        let result = self.phase == Phase::Finalization_Feldman;

        if !result {
            trace!("incompleted DKG session containing:");
            for (key, part) in self.parts.iter() {
                let val = part.value;
                trace!("    Part from {:?}, and acks from {:?}", key, val);
            }
        }
        result
    }

    /// Returns the new secret key share and the public key set.
    pub fn generate_keys(&self) -> Option<(Vec<BTreeSet<XorName>>, Outcome)> {
        if !self.is_finalized() {
            return None;
        }

        let mut pk_commitment = Poly::zero().commitment();
        let mut sk_val = Fr::zero();


        for i in 0..self.tribe.len(){

            let clan: Vec<_> = self.tribe[i].iter().cloned().collect();
            for j in 0..clan.len(){

                if !self.disqual_set.contains(&clan[j]){

                    let contribution = self.parts.get(&(i as u64, j as u64)).unwrap();
                    pk_commitment += contribution.commitment_feldman.clone();
                    sk_val.add_assign(contribution.value);

                }
            }
        }

        if pk_commitment.evaluate(self.our_index.1 + 1)
            != G1Affine::generator().mul(sk_val)
        {
            return None;
        }

        let sk = SecretKeyShare::from_mut(&mut sk_val);

        Some((
            self.tribe.clone(),
            Outcome::new(pk_commitment.into(), sk, (self.our_index.0 as usize, self.our_index.1 as usize) ),
        ))
    }

    /// This function shall be called when the DKG procedure not reach Finalization phase and before
    /// discarding the instace. It returns potential invalid peers that causing the blocking, if
    /// any and provable.
    /*
    pub fn possible_blockers(&self) -> BTreeSet<XorName> {
        let mut result = BTreeSet::new();
        match self.phase {
            Phase::Initialization => {


                for i in 0..self.tribe.len() {
                    let clan: Vec<_> = self.tribe[i].iter().cloned().collect();

                    for j in 0..clan.len(){

                        if !self
                            .initalization_accumulator
                            .senders
                            .contains(&(i as u64, j as u64))
                        {
                            let name = self.node_id_from_index((i as u64, j as u64)).unwrap();
                            let _ = result.insert(name);
                        }

                    }
                }

            }
            Phase::Contribution_Pedersen => result = self.non_contributors().1,
            Phase::Complaining_Pedersen => {
                // Non-voters shall already be returned within the error of the
                // finalize_complaint_phase function call.
            }
            Phase::Justification_Pedersen  => {
                // As Complaint phase gets completed, it is expected that all nodes are now
                // in these two phases. Hence here a strict rule is undertaken that: any missing
                // vote will be considered as a potential non-voter.
                for part in self.parts.values() {
                    for (index, name) in self.names.iter().enumerate() {
                        if !part.acks.contains(&(index as u64)) {
                            let _ = result.insert(*name);
                        }
                    }
                }
            }
            Phase::Finalization_Feldman => {
                // Not blocking
            }
        }
        result
    }
*/
    /// Handles a `Part`, returns a `PartFault` if it is invalid.
    fn handle_part_or_fault(
        &mut self,
        sender_index: (u64, u64),
        Part {
            receiver,
            commitment_pedersen,
            commitment_feldman,
            point_eval,
            point_eval_prime,
        }: Part,
    ) -> Result<Option<Fr>, PartFault> {

        if receiver != self.our_index {
            return Ok(None);
        }

        if let Some(state) = self.parts.get(&sender_index) {
            if state.commitment_pedersen != commitment_pedersen {
                return Err(PartFault::MultipleParts);
            }
            return Ok(None); // We already handled this `Part` before.
        }

        let val = deserialize::<FieldWrap<Fr>>(&point_eval)
            .map_err(|_| PartFault::DeserializeValue)?
            .into_inner();

        let val_prime = deserialize::<FieldWrap<Fr>>(&point_eval_prime)
            .map_err(|_| PartFault::DeserializeValue)?
            .into_inner();

        if commitment_pedersen.evaluate(self.our_index.1 + 1)
            != (G1Affine::generator().mul(val) + self.h.mul(val_prime))
        {
            return Err(PartFault::ShareVerify);
        }

        let _ = self
            .parts
            .insert(sender_index, ProposalState::new(commitment_pedersen));

        let part = self
            .parts
            .get_mut(&sender_index)
            .ok_or(PartFault::MissingPart)?;

        let _ = part.value = val;
        let _ = part.value_prime = val_prime;


        Ok(Some(val))
    }

    /// Handles a `Part`, returns a `PartFault` if it is invalid.
    fn handle_part_or_fault_feldman(
        &mut self,
        sender_index: (u64, u64),
        Part {
            receiver,
            commitment_pedersen,
            commitment_feldman,
            point_eval,
            point_eval_prime,
        }: Part,
    ) -> Result<Option<Fr>, PartFault> {

        // If sender is not in Qual Set
        if self.disqual_set.contains(&self.node_id_from_index(sender_index).unwrap()) {
            return Ok(None);
        }

        if receiver != self.our_index {
            return Ok(None);
        }

        if let Some(state) = self.parts.get(&sender_index) {

            if commitment_feldman.evaluate(self.our_index.1 + 1)
                != G1Affine::generator().mul(state.value)
            {
                return Err(PartFault::ShareVerify);
            }
            else {

                let part = self
                    .parts
                    .get_mut(&sender_index)
                    .ok_or(PartFault::MissingPart)?;

                let _ = part.commitment_feldman = commitment_feldman;
                return Ok(Some(part.value));
            }
        }

        return Ok(None);

    }


}

impl Debug for KeyGen {
    fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
        write!(formatter, "KeyGen{{{:?}}}", self.our_id)
    }
}

#[cfg(test)]
impl KeyGen {
    /// Returns the name list of the final participants.
    pub fn names(&self) -> &Vec<BTreeSet<XorName>> {
        &self.tribe
    }

    /// Initialize an instance with some pre-defined value, only for testing usage.
    pub fn initialize_for_test(
        our_id: XorName,
        total_clans: usize,
        tribe_threshold: usize,
        clan_threshold: usize,
        our_index: (u64, u64),
        tribe: Vec<BTreeSet<XorName>>,
        h: G1,
        phase: Phase,
    ) -> KeyGen {
        assert!(tribe.len() > tribe_threshold);

        let mut total_members :usize = 0;
        let mut names: BTreeMap<XorName, (u64,u64)> = BTreeMap::new();

        for i in 0..tribe.len() {
            let clan: Vec<_> = tribe[i].iter().cloned().collect();
            assert!((*clan).len() > clan_threshold);
            for j in 0..clan.len(){
                total_members = total_members+1;
                names.insert(clan[j], (i as u64, j as u64));

            }
        }

        KeyGen {
            our_id,
            our_index,
            our_part: BivariatePolynomial::zero(),
            our_part_pedersen: BivariatePolynomial::zero(),
            tribe: tribe.clone(),
            names: names.clone(),
            total_members,
            parts: BTreeMap::new(),
            tribe_threshold,
            h,
            clan_threshold,
            disqual_set: BTreeSet::new(),
            phase,
            initalization_accumulator: InitializationAccumulator::new(total_clans),
            complaints_accumulator: ComplaintsAccumulatorPedersen::new(tribe.clone()),
            complaints_accumulator_feldman: ComplaintsAccumulatorFeldman::new(),
            pending_complain_messages: Vec::new(),
            message_cache: BTreeMap::new(),
        }
    }
}


/// `Part` faulty entries.
#[non_exhaustive]
#[derive(
    Clone, Copy, Eq, thiserror::Error, PartialEq, Debug, Serialize, Deserialize, PartialOrd, Ord,
)]
pub enum PartFault {

    ///Share verification fails
    #[error("Verification of point share using the commitment fails")]
    ShareVerify,
    /// No corresponding Part received.
    #[error("No corresponding Part received")]
    MissingPart,
    /// The number of rows differs from the number of nodes.
    #[error("The number of rows differs from the number of nodes")]
    RowCount,
    /// Value deserialization failed.
    #[error("Value deserialization failed")]
    DeserializeValue,
    /// Received multiple different Part messages from the same sender.
    #[error("Received multiple different Part messages from the same sender")]
    MultipleParts,
    /// Could not decrypt our row in the Part message.
    #[error("Could not decrypt our row in the Part message")]
    DecryptRow,
    /// Could not deserialize our row in the Part message.
    #[error("Could not deserialize our row in the Part message")]
    DeserializeRow,
    /// Row does not match the ack.
    #[error("Row does not match the ack")]
    RowAcknowledgment,
}

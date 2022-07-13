// Copyright (c) 2022, MaidSafe.
// All rights reserved.
//
// This SAFE Network Software is licensed under the BSD-3-Clause license.
// Please see the LICENSE file for more details.

use super::encryptor::{Iv, Key};
use super::{Part};
use serde_derive::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use blsttc::poly::Commitment;
use tiny_keccak::{Hasher, Sha3};
use xor_name::XorName;


/// SHA3-256 hash digest.
type Digest256 = [u8; 32];

/// Messages used for running BLS DKG. //PartialOrd, Ord,
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub enum Message {
    Initialization {
        key_gen_id: (u64,u64),
        m1: usize,
        n1: usize,
        m2: usize,
        n2: usize,
        member_list: Vec<BTreeSet<XorName>>,
    },
    Proposal {
        key_gen_id: (u64,u64),
        part: Part,
    },

    Proposal_Feldman {
        key_gen_id: (u64,u64),
        part: Part,
    },

    Complaint {
        key_gen_id: (u64,u64),
        target: (u64,u64),
        msg: Vec<u8>,
    },

    Complaint_Feldman {
        key_gen_id: (u64,u64),
        target: (u64,u64),
        point_eval: Vec<u8>,
        point_eval_prime: Vec<u8>,
    },



    Justification {
        key_gen_id: (u64,u64),
        contribution: BTreeMap<XorName, (Vec<u8>, Vec<u8>, Commitment)>,
    },

    Reconstruction {
        key_gen_id: (u64,u64),
        complained_node: XorName,
        point_eval: Vec<u8>,
    },
}

impl Message {
    // Creator of the message.
    pub fn creator(&self) -> (u64, u64) {
        match &*self {
            Message::Initialization { key_gen_id, .. }
            | Message::Proposal { key_gen_id, .. }
            | Message::Proposal_Feldman { key_gen_id, .. }
            | Message::Complaint { key_gen_id, .. }
            | Message::Complaint_Feldman { key_gen_id, .. }
            | Message::Justification { key_gen_id, .. }
            | Message::Reconstruction {key_gen_id, ..} => *key_gen_id,

        }
    }

    // Identifier of the message.
    pub fn id(&self) -> XorName {
        let mut hasher = Sha3::v256();
        let mut hash = Digest256::default();

        if let Ok(serialized) = bincode::serialize(self) {
            hasher.update(&serialized);
            hasher.finalize(&mut hash);
        }

        XorName::from_content(&hash)
    }
}

impl fmt::Debug for Message {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &*self {
            Message::Initialization {
                key_gen_id,
                member_list,
                ..
            } => write!(
                formatter,
                "Initialization({:?} - {:?})",
                member_list, key_gen_id
            ),
            Message::Proposal { key_gen_id, part } => {
                write!(formatter, "Proposal({} {} - {:?})", key_gen_id.0, key_gen_id.1, part)
            }
            Message::Proposal_Feldman { key_gen_id, part } => {
                write!(formatter, "Proposal({} {} - {:?})", key_gen_id.0, key_gen_id.1, part)
            }
            Message::Complaint {
                key_gen_id, target, ..
            } => write!(formatter, "Complaint({} {} - {} {})", key_gen_id.0, key_gen_id.1, target.0, target.1),
            Message::Complaint_Feldman {
                key_gen_id, target, ..
            } => write!(formatter, "Complaint_Feldman({} {} - {} {})", key_gen_id.0, key_gen_id.1, target.0, target.1),
            Message::Justification { key_gen_id, .. } => {
                write!(formatter, "Justification({} {})", key_gen_id.0, key_gen_id.1)
            }
            Message::Reconstruction { key_gen_id, .. } => {
                write!(formatter, "Reconstruction({} {})", key_gen_id.0, key_gen_id.1)
            }


        }
    }
}

//! darkprep: real preprocessing for the dark-learning MPC fork, replacing the ideal dealer
//! (`research/dark_learning_2026_11_06/spdz.py` `Dealer`).
//!
//! Backend: MP-SPDZ's MASCOT (OT-based, malicious security with abort, dishonest majority) over the
//! SPDZ prime p (61 bits). `mpc/darkprep.mpc` is run by three `mascot-party.x` processes on 127.0.0.1;
//! each writes its authenticated shares to `Persistence/Transactions-P<i>.data`. This crate reads that
//! party-local file and assembles the party's TAPE in the online step's program order ([`schedule`]).
//!
//! Tape format (`tape-P<i>.bin`, little-endian), the logical format the online step consumes:
//! ```text
//!   magic  b"DLTAPE1\n"
//!   u64 p, u32 n_parties, u32 party, u64 alpha_i
//!   u32 d, u8 inputs_mode (0 = harness: W1, W2, x, y input every step; 1 = steady: x, y only),
//!   4 x (u8 s, u8 K)  the truncation parameters (S1,K1), (S1,K1), (S2,K2), (S3,K3)
//!   u64 n_entries, then n_entries x (u8 tag, u64 share, u64 mac_share)     [17 bytes each]
//! ```
//! Tags (code, name): 0 in, 1 ta, 2 tb, 3 tc, 4 tr, 5 trb, 6 trh, 7 lp, 8 ar. Values are canonical
//! residues in [0, p). The data owner's tape (`owner.bin`): magic b"DLOWNR1\n", u64 p, u64 n, then n x u64 r,
//! one per "in" entry in order: the input mask the owner learned (after checking a b = c, see [`owner`]).

pub mod field;
pub mod mpspdz;
pub mod owner;
pub mod schedule;
pub mod tape;
pub mod verify;

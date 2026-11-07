//! # dzkpopk: the batched Ligero ZKPoPK and the key ceremony
//!
//! Native port of `research/dark_learning_2026_11_06/zkpopk_ligero.py` and `keygen_ceremony.py` (decision doc
//! §20.2, §21.1). Proof bytes are bit-exact with the harness: with the same statement and the harness's
//! `DL_DETERMINISTIC=<seed>` hook mirrored by [`ProveOpts::det_seed`], native and Python produce identical bytes,
//! and each verifies the other's proofs.
//!
//! ## Relation
//! * `Kind::Sk` (the MPC helpers' sends): registered key `b + a s + e_pk = 0`, `a = public_a(seed)`; per ciphertext
//!   `t (c0 + c1 s + e) - r = 0 (mod q_i)` with r zero off the public slot set; s ternary, e, e_pk in [-8, 8],
//!   |r| <= (t-1)/2. Together: the plaintext is zero off the layout, |e| <= 8, one integer s across limbs and key.
//! * `Kind::Pk` (FHE (b) masks under the joint key): `t (c0 - b u - e0) - r = 0`, `c1 - a u - e1 = 0`.
//! * `Kind::Key` (the ceremony): the key relation alone.
//!
//! ## API (what a custodian process calls)
//! ```ignore
//! use dzkpopk::*;
//! let reg = std::sync::Arc::new(KeyRegistry::new(n, &primes, t, &seed, "custodian-1", b));   // the pinned record
//! let st = Statement::new(reg, Kind::Sk, cts, slots, context)?;   // the recipient builds this from ITS OWN context
//! let proof: Vec<u8> = prove(&st, &witness, T_LEDGER)?;          // sender
//! verify(&st, &proof, T_LEDGER)?;                                 // recipient gate, before any ptxct; Err(reason)
//! ```
//! Ciphertexts are [`BigPoly`]s (canonical integers < Q; [`BigPoly::from_rns`] builds them from residues).
//! The context is a [`Json`] value hashed canonically (as `scholar_zkpopk.canonical`).
//!
//! ## Profiles
//! `T_LEDGER = 309` columns (2^-128.25, 3 folds) is the default; `T_DEMO = 97` (2^-40.26 statistical, 1 fold).
//! Proof bytes = [`proof_bytes`] of the [`shape`], checked on every proof.
//!
//! ## Ceremony
//! [`ceremony::Ceremony`] (commit, reveal, seed, register with the key proof), [`ceremony::Custodian`]
//! (`commitment`, `make_key`), [`ceremony::run_ceremony`].
//!
//! Everything under `Cheat`, `ProveOpts::legacy`, `simulate_legacy` and `verify_opts(.., legacy = true)` exists
//! for the attack table only.

pub mod canon;
pub mod ceremony;
pub mod field;
pub mod gen;
pub mod ntt;
pub mod proof;
pub mod rng;
pub mod statement;
pub mod transcript;
pub mod vectors;

pub use canon::Json;
pub use proof::{prove, prove_with, simulate_legacy, verify, verify_opts, Cheat, PkCt, ProveOpts, SkCt, Vals, Witness};
pub use statement::{batch_proof_bits, folds_for, proof_bytes, shape, BigPoly, KeyRegistry, Kind, Shape, Statement};

/// The ledger profile: T = 309 opened columns, 2^-128.25, folds_for(309) = 3.
pub const T_LEDGER: usize = 309;
/// The demo profile: T = 97, 2^-40.26 statistical, one fold.
pub const T_DEMO: usize = 97;

//! Native MPC-fork custodians for dark learning (see native/README.md). The Python harness
//! (research/dark_learning_2026_11_06) is the bit-exact reference: `native_ref.py` there.
pub mod arith;
pub mod bfv;
pub mod ntt;
pub mod rns;
pub mod he;
pub mod net;
pub mod party;
pub mod step;
pub mod tape;
pub mod node;
pub mod gate;

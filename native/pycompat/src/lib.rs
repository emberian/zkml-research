//! Bit-exact CPython compatibility shims for the dark-learning native port (zkml-research
//! research/dark_learning_2026_11_06 is the reference).
pub mod random;
pub mod repr;
pub use random::PyRandom;
pub use repr::ReprHasher;

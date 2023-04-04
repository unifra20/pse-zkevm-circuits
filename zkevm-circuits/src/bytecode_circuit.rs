//! The bytecode circuit implementation.

/// Bytecode unroller
pub mod bytecode_unroller;
/// Bytecode circuit
pub mod circuit;

/// chiquito version of circuit
pub mod ccircuit;

/// Bytecode circuit tester
#[cfg(any(feature = "test", test))]
pub mod dev;
pub(crate) mod param;
mod wit_gen;

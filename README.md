# Lean-for-Lean

This is an implementation of the Lean 4 kernel written in (mostly) pure Lean 4.
It is derived directly from the C++ kernel implementation, and as such likely
shares some implementation bugs with it (it's not really an independent
implementation), although it also benefits from the same algorithmic performance
improvements existing in the C++ Lean kernel.

The project aspires to eventually also house some metatheory regarding the Lean
system, in the same general direction as the
[MetaCoq project](https://github.com/MetaCoq/metacoq/).

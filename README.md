# Dataflow Analysis in Lean

Subset of TIP as defined in _Static Program Analysis_. Approach influenced by _Principles of Program Analysis_.

The goal is to develop complete, end-to-end proofs of dataflow soundness in Lean, establishing correctness of the procedure (fixpoint computation) as well as correctness wrt language semantics.

Implemented so far : 

- Subset of TIP : syntax and CEK semantics.
- CFG builder
- Kildall's Worklist algorithm (verified to be terminating and sound)
- Generic dataflow framework
- Decorated semantics over the CEK semantics, proven equivalent to the original
- Two analyses (Constant Propagation, Collection Semantics)
- Correctness for the two analyses!

Remains:
- [ ] Lots Lots Lots of cleanup
  - [ ] Unify fixpoint definitions
  - [ ] Simplify instantiation
  - [ ] Generalize approach for more languages
- [ ] Galois connections between collection semantics and further analyses for more composable proofs.

## Structure of this project

- `Flow/Lang/`: syntax, CEK semantics, CFGs, and CFG construction.
- `Flow/Eval/`: decorated semantics and collection-style semantics.
- `Flow/Analysis/`: the abstract interpretation framework, worklist solver, and constant propagation.
- `Flow.lean`: umbrella import for the `Flow/` library.



# Dataflow Analysis in Lean

Subset of TIP as defined in _Static Program Analysis_. Approach influenced by _Principles of Program Analysis_.

The goal is to develop complete, end-to-end proofs of dataflow soundness in Lean, establishing correctness of the procedure (fixpoint computation) as well as correctness wrt language semantics.

Progress:
- [x] Formalized Kildall's worklist algorithm. 
  - [x] Proof of termination
  - [x] Proof of soundness
- [x] Example of "mundane" correctness as described in PPA.
  - [x] Constant propagation
- [ ] Collection semantics proven by "mundane" correctness
- [ ] Galois connections between collection semantics and further analyses.


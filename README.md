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

## Structure of this project

```
Flow/
  Analysis/ -- generic, language-agnostic framework
    Lattice.lean                       (FiniteHeight, LatticeLike, Domain, StateN)
    Worklist.lean                      (algorithm)
    WorklistProofs.lean                (mono/invariant/soundness/completeness)
    Generic.lean                       (generic correctness of the algorithm)
    Utils.lean
  TIP/  -- concrete language
    Defs.lean, LangSem.lean, Eval.lean (syntax + cek semantics)
    CFG.lean                           (cfg Builder and well formedness)
    Correspondence/
      Refinement.lean, Located.lean    (cek <-> cfg semantic refinement)
    Analyses/
      CP.lean, Collection.lean         (example analyses)
    Examples/SimpleProgram.lean        (application)
    Utils/DotPrinter.lean
```

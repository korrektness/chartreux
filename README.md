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
    Generic.lean                       (generic correctness of the algorithm)
    Lattice.lean                       (FiniteHeight, LatticeLike, Domain, StateN)
    Utils.lean
    Worklist.lean                      (algorithm)
    WorklistProofs.lean                (mono/invariant/soundness/completeness)
  TIP/ -- concrete language and analyses
    Defs.lean, Eval.lean               (syntax + cek semantics)
    Big/
      CFG.lean
    Examples/ (applications)
    Regular/
      CFG.lean, LangSem.lean
      Analyses/
        Collection.lean, CP.lean       (example analyses)
      Correspondence/
        Located.lean, Refinement.lean   (CEK <-> CFG semantic refinement)
    Utils/ (dot printers)
```

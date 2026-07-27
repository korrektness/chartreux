# Dataflow Analysis in Lean

Subset of TIP as defined in _Static Program Analysis_. Approach influenced by _Principles of Program Analysis_.

The goal is to develop complete, end-to-end proofs of dataflow soundness in Lean, establishing correctness of the procedure (fixpoint computation) as well as correctness wrt language semantics.

Implemented so far : 

- Subset of TIP : syntax and CEK semantics.
- CFG builder
- Kildall's Worklist algorithm (verified to be terminating and sound)
- Generic dataflow framework
- Decorated semantics over the CEK semantics, proven equivalent to the original
- Implementation and correctness for Constant Propagation, over the original language

## Structure of this project

```
Chartreux/
  Analysis/
    Generic.lean                       (generic correctness of the algorithm)
    Lattice.lean                       (FiniteHeight, LatticeLike, Domain, StateN)
    Utils.lean
    Worklist.lean                      (algorithm)
    WorklistProofs.lean                (mono/invariant/soundness/completeness)
  TIP/
    Defs.lean, Eval.lean               (syntax + cek semantics)
    Examples/
    Regular/
      CFG.lean, LangSem.lean
      Analyses/
        Collection.lean, CP.lean       (example analyses)
      Correspondence/
        Located.lean, Refinement.lean   (CEK <-> CFG semantic refinement)
    Utils/ (dot printer)
```

## Contributing

You can add the following script to your `.git/hooks` folder, to check the CI for warnings before committing.

```sh
#!/bin/sh

set -u

# build project
lake build --fail-level=warning

if [ $? -ne 0 ]
then
  cat <<\EOF
    [[ PRE-COMMIT ]] Build failed.
EOF
  
  exit 1
fi
```


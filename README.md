# Chartreux : Verified Dataflow Analysis in Lean

Chartreux is a framework for specifying and verifying dataflow analyses on control flow graphs, implemented in Lean. It rests on abstract representations for CFGs, and a verified implementation of Kildall's algorithm, to derive analysis correctness with respect to language semantics.

## Structure

```
Chartreux/
  Analysis/
    Generic.lean
    Lattice.lean
    Utils.lean
    Worklist.lean
    WorklistProofs.lean
  Duke/
    Analyses/
    Examples/
    Defs.lean, CFG.lean, ...
README.md
```

The `Analysis/` directory contains the abstract framework and all of the relevant proofs of correctness that back it. A sample instantiation lives in `Duke/`, based on a minimal subset of the Kotlin programming language, and an analysis lifted from its compiler.

## Background

A presentation of the framework and its applications to the Kotlin programming language can be found in the paper, a link to which will be provided shortly.

#### Namesake

The framework is named after the [Chartreux](https://en.wikipedia.org/wiki/Chartreux) breed of cats, which seems to be the breed of the protagonist from the movie [Flow](https://en.wikipedia.org/wiki/Flow_(2024_film)). The ties between the movie's title and this work should be relatively straightforward.

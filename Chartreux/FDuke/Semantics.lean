import Chartreux.FDuke.Eval

/-!
# The κ-graph

Generated CFGs contain only structural edges, so the κ-graph (`CFG.kappa`) is
the identity view used by dataflow analyses.
-/

open Chartreux.Analysis Chartreux.Analysis.Generic

/-- The structural identity view used by analyses. -/
def CFG.kappa (g : CFG) : CFG := g

@[simp] theorem CFG.kappa_nodes (g : CFG) : g.kappa.nodes = g.nodes := rfl
@[simp] theorem CFG.kappa_entry (g : CFG) : g.kappa.entry = g.entry := rfl
@[simp] theorem CFG.kappa_exit (g : CFG) : g.kappa.exit = g.exit := rfl
@[simp] theorem CFG.kappa_nodeKind (g : CFG) (n : NodeID) :
    g.kappa.nodeKind n = g.nodeKind n := rfl

theorem CFG.kappa_edges_mem {g : CFG} {e : Edge} :
    e ∈ g.kappa.edges ↔ e ∈ g.edges := by
  rfl

/-- The structural identity view preserves well-formedness. -/
theorem CFG.kappa_WF {g : CFG} (hg : g.WellFormed) : g.kappa.WellFormed := by
  exact hg

/-- The κ-graph of a well-formed CFG, packaged with its `WellFormed` proof. -/
def WFCFG.kappa (g : WFCFG) : WFCFG := ⟨g.val.kappa, CFG.kappa_WF g.prop⟩

/-- The store-only step read off a node of the κ-graph: an ordinary
    `IntraStep`, or a store-identity step out of a `Call` node. Structural
    call edges are the way through a call site: `en → enL` hands
    the caller's store to the inlined lambda copy, and the `?`/`ε` bypass
    `en → r` skips it; both leave the store untouched (the call's store effect
    materialises through the inlined body runs, cf.
    `Chartreux.FDuke.Refinement`). -/
def KappaStep (cfg : CFG) (n : NodeID) (σ σ' : State) : Prop :=
  IntraStep cfg n σ σ' ∨
  ((∃ f ℓ, cfg.nodeKind n = some (.Call f ℓ)) ∧ σ' = σ)

@[simp] theorem WFCFG.kappa_analysis_entry (g : WFCFG) :
    g.kappa.analysis.entry = g.analysis.entry := rfl

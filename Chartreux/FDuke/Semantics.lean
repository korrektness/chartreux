import Chartreux.FDuke.Eval

/-!
# The κ-graph: a CFG without its summary edges

The *κ-graph* (`CFG.kappa`) of a callee CFG is the graph with its `.summary`
edges removed: every remaining edge is `.plain`, so an `LStep` over it is
always an `IntraStep` and never an opaque `CallSummary`. This is the graph
that dataflow analyses — in particular the counting analysis of
`Chartreux.FDuke.Counting` — actually run on, while the full graph (with its
summary edge) stays the semantic anchor targeted by the CEK projection.
-/

open Chartreux.Analysis Chartreux.Analysis.Generic

/-- `g` with its `.summary` edges removed. This is the graph analyses run on:
    every remaining edge is `.plain`, so an `LStep` over it is always an
    `IntraStep` and never an opaque `CallSummary`. -/
def CFG.kappa (g : CFG) : CFG :=
  { g with edges := g.edges.filter (·.kind = EdgeLabel.plain) }

@[simp] theorem CFG.kappa_nodes (g : CFG) : g.kappa.nodes = g.nodes := rfl
@[simp] theorem CFG.kappa_entry (g : CFG) : g.kappa.entry = g.entry := rfl
@[simp] theorem CFG.kappa_exit (g : CFG) : g.kappa.exit = g.exit := rfl
@[simp] theorem CFG.kappa_nodeKind (g : CFG) (n : NodeID) :
    g.kappa.nodeKind n = g.nodeKind n := rfl

theorem CFG.kappa_edges_mem {g : CFG} {e : Edge} :
    e ∈ g.kappa.edges ↔ e ∈ g.edges ∧ e.kind = .plain := by
  simp [kappa, List.mem_filter]

/-- Removing summary edges preserves well-formedness: bounds restrict to a
    sublist, the plain-progress condition only mentions `.plain` edges (which
    all survive), and the summary condition becomes vacuous. -/
theorem CFG.kappa_WF {g : CFG} (hg : g.WellFormed) : g.kappa.WellFormed := by
  obtain ⟨hentry, hsrc, hdst, hout, hsum, hexit⟩ := hg
  refine ⟨hentry, ?_, ?_, ?_, ?_, hexit⟩
  · intro e he; exact hsrc e (kappa_edges_mem.mp he).1
  · intro e he; exact hdst e (kappa_edges_mem.mp he).1
  · intro n hn hne
    obtain ⟨n', hn'⟩ := hout n hn hne
    exact ⟨n', kappa_edges_mem.mpr ⟨hn', rfl⟩⟩
  · intro e he hk; exact hsum e (kappa_edges_mem.mp he).1 hk

/-- The κ-graph of a well-formed CFG, packaged with its `WellFormed` proof. -/
def WFCFG.kappa (g : WFCFG) : WFCFG := ⟨g.val.kappa, CFG.kappa_WF g.prop⟩

/-- The store-only step read off a node of the κ-graph: an ordinary
    `IntraStep`, or — specific to the κ-graph — a store-identity step out of a
    `Call` node. On the full graph a `Call` node's outgoing `.plain` κ edges
    are dead (the call's runtime meaning lives on its `.summary` edge), but on
    the κ-graph they are the *only* way through a call site: `en → enL` hands
    the caller's store to the inlined lambda copy, and the `?`/`ε` bypass
    `en → r` skips it; both leave the store untouched (the call's store effect
    materialises through the inlined body runs, cf.
    `Chartreux.FDuke.Refinement`). -/
def KappaStep (cfg : CFG) (n : NodeID) (σ σ' : State) : Prop :=
  IntraStep cfg n σ σ' ∨
  ((∃ f ℓ, cfg.nodeKind n = some (.Call f ℓ)) ∧ σ' = σ)

@[simp] theorem WFCFG.kappa_analysis_entry (g : WFCFG) :
    g.kappa.analysis.entry = g.analysis.entry := rfl

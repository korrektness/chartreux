import Chartreux.FDuke.Defs
import Chartreux.Analysis.CFG

-- # Defs
abbrev NodeID := Nat

inductive CFGRef where
| main
| fn  (f : String)
| lam (ℓ : Nat)
deriving DecidableEq, Repr

inductive NodeKind where
| Assume (e : FExpr)
| Assign (x : String) (e : FExpr)
| Skip
| Call (f : String) (ℓ : Nat)
| Invoke
deriving DecidableEq, Repr

/-- Compatibility label for structural edges. -/
inductive EdgeLabel where
| plain
deriving DecidableEq, Repr

structure Edge where
  src : NodeID
  dst : NodeID
  kind : EdgeLabel := .plain
deriving DecidableEq, Repr

structure CFG where
  nodes : List NodeKind
  edges : List Edge
  entry : NodeID
  exit  : NodeID
deriving DecidableEq, Repr

def CFG.inEdges (g : CFG) (n : NodeID) : List Edge :=
  g.edges.filter (·.dst = n)
def CFG.nodeKind (g : CFG) (n : NodeID) : Option NodeKind :=
  g.nodes[n]?

/-- Construction-time provenance for one κ-gadget emitted for a `call` site. -/
structure CallGadget where
  en : NodeID
  f : String
  lamID : Nat
  kappa : InvKind
  enL : NodeID
  exL : NodeID
  ret : NodeID
  body : Stmt
deriving DecidableEq, Repr


def CFG.WellFormed (g : CFG) :=
  (g.entry < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.src < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.dst < g.nodes.length) ∧
  (∀ n < g.nodes.length, n ≠ g.exit → ∃ n', (⟨n, n', .plain⟩ : Edge) ∈ g.edges) ∧
  (g.exit < g.nodes.length)

abbrev WFCFG := { cfg : CFG // cfg.WellFormed }


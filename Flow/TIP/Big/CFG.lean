import Flow.TIP.Regular.CFG
import Flow.Analysis.Lattice
import Mathlib.Tactic.Lemma
import Mathlib.Data.List.Nodup

inductive BigNodeKind where
| SEntry (s : Stmt)
| SExit
| EEntry (e : Expr)
| EExit
deriving DecidableEq, Repr

abbrev BigNodeID := Nat

structure BigCFG where
  nodes : List BigNodeKind
  edges : List Edge
  entry : Nat
  exit : Nat

namespace BigCFG
def nodeKind (g : BigCFG) (n : BigNodeID) : Option BigNodeKind :=
  g.nodes[n]?
def succ (g : BigCFG) (n : BigNodeID) : List BigNodeID :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if src = n then dst else none)
def pred (g : BigCFG) (n : BigNodeID) : List BigNodeID :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if dst = n then src else none)
def hasEdge (g : BigCFG) (src dst : BigNodeID) (k : EdgeKind) : Prop :=
  ⟨src, dst, k⟩ ∈ g.edges
end BigCFG

structure BigCFGBuilder where
  cfg : BigCFG

namespace BigCFGBuilder
def empty : BigCFGBuilder := {
  cfg := ⟨[], [], 0, 0⟩,
}

-- builder monad
abbrev BuilderM := StateM BigCFGBuilder

def freshNode (k : BigNodeKind) : BuilderM BigNodeID := do
  let b ← get
  set { b with cfg := { b.cfg with nodes := b.cfg.nodes ++ [k]} }
  return b.cfg.nodes.length

def emitEdge (s d : BigNodeID) (k : EdgeKind) : BuilderM Unit :=
  modify fun b => { b with cfg := { b.cfg with edges := b.cfg.edges ++ [⟨s, d, k⟩] } }

def buildExpr : Expr → BuilderM (BigNodeID × BigNodeID)
| .Var x => do
    let en ← freshNode (.EEntry (.Var x))
    let ex <- freshNode (.EExit)
    emitEdge en ex .Normal
    return (en, ex)
| .Int n => do
    let en ← freshNode (.EEntry (.Int n))
    let ex <- freshNode (.EExit)
    emitEdge en ex .Normal
    return (en, ex)
| .BinOp o e₁ e₂ => do
    let en   ← freshNode (.EEntry (.BinOp o e₁ e₂))
    let (en₁, ex₁) ← buildExpr e₁
    let (en₂, ex₂) ← buildExpr e₂
    let ex   ← freshNode .EExit
    emitEdge en  en₁ .Normal
    emitEdge ex₁ en₂ .Normal
    emitEdge ex₂ ex  .Normal
    return (en, ex)

def assignGraph (x : String) (e : Expr) : BuilderM (BigNodeID × BigNodeID) := do
  let en ← freshNode (.SEntry (.Assign x e))
  let (een, eex) ← buildExpr e
  let ex ← freshNode .SExit
  emitEdge en een .Normal
  emitEdge eex ex .Normal
  return (en, ex)

def declGraph (x : String) (e : Expr) : BuilderM (BigNodeID × BigNodeID) := do
  let en ← freshNode (.SEntry (.Decl x e))
  let (een, eex) ← buildExpr e
  let ex ← freshNode .SExit
  emitEdge en een .Normal
  emitEdge eex ex .Normal
  return (en, ex)

def buildStmt : Stmt → BuilderM (BigNodeID × BigNodeID)
| .Skip => do
    let en <- freshNode (.SEntry .Skip)
    return (en, en)
| .Assign x e => do
    let en ← freshNode (.SEntry (.Assign x e))
    let (een, eex) ← buildExpr e
    let ex ← freshNode .SExit
    emitEdge en een .Normal
    emitEdge eex ex .Normal
    return (en, ex)
| .Decl x e => do
    let en ← freshNode (.SEntry (.Decl x e))
    let (een, eex) ← buildExpr e
    let ex ← freshNode .SExit
    emitEdge en een .Normal
    emitEdge eex ex .Normal
    return (en, ex)
| .Seq s₁ s₂ => do
    let (en₁, ex₁) <- buildStmt s₁
    let (en₂, ex₂) <- buildStmt s₂
    emitEdge ex₁ en₂ .Normal
    return (en₁, ex₂)
| .If c tb fb => do
    let en           <-  freshNode (.SEntry (.If c tb fb))
    let (cen, cex)   <- buildExpr c
    let (en_t, ex_t) <- buildStmt tb
    let (en_f, ex_f) <- buildStmt fb
    let nexit        <- freshNode .SExit
    emitEdge en cen .Normal
    emitEdge cex en_t .TBranch
    emitEdge cex en_f .FBranch
    emitEdge ex_t nexit .Normal
    emitEdge ex_f nexit .Normal
    return (en, nexit)
| .While c b => do
    let en           <- freshNode (.SEntry (.While c b))
    let (cen, cex)   <- buildExpr c
    let (en_b, ex_b) <- buildStmt b
    let nexit        <- freshNode .SExit
    emitEdge en cen .Normal
    emitEdge cex en_b .TBranch
    emitEdge ex_b cen .Normal
    emitEdge cex nexit .FBranch
    return (en, nexit)

end BigCFGBuilder

namespace BigCFG

def WellFormed (g : BigCFG) : Prop :=
  g.entry < g.nodes.length ∧
  (∀ e ∈ g.edges, e.src < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.dst < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.dst ≠ g.entry)

instance (g : BigCFG) : Decidable g.WellFormed := by
  unfold WellFormed; infer_instance

/-- Build a BigCFG from a `Stmt` using the empty builder. -/
def ofStmt (s : Stmt) : BigCFG :=
  let ((en, ex), b) := (BigCFGBuilder.buildStmt s).run BigCFGBuilder.empty
  { b.cfg with entry := en, exit := ex }

def ofStmt_WF (s : Stmt) : (BigCFG.ofStmt s).WellFormed := by
  -- TODO: well-formedness
  sorry

end BigCFG

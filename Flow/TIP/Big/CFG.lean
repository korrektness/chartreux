import Flow.TIP.Defs
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

inductive EdgeKind where
| Normal
| TBranch
| FBranch
deriving DecidableEq, Repr

structure Edge where
  src : BigNodeID
  dst : BigNodeID
  kind : EdgeKind
deriving DecidableEq, Repr

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
  let b <- get
  set { b with cfg := { b.cfg with nodes := b.cfg.nodes ++ [k]} }
  return b.cfg.nodes.length

def emitEdge (s d : BigNodeID) (k : EdgeKind) : BuilderM Unit :=
  modify fun b => { b with cfg := { b.cfg with edges := b.cfg.edges ++ [⟨s, d, k⟩] } }

@[simp] lemma freshNode_fst (k : BigNodeKind) (b : BigCFGBuilder) :
    ((BigCFGBuilder.freshNode k).run b).1 = b.cfg.nodes.length := rfl

@[simp] lemma freshNode_nodes (k : BigNodeKind) (b : BigCFGBuilder) :
    ((BigCFGBuilder.freshNode k).run b).2.cfg.nodes = b.cfg.nodes ++ [k] := rfl

@[simp] lemma freshNode_edges (k : BigNodeKind) (b : BigCFGBuilder) :
    ((BigCFGBuilder.freshNode k).run b).2.cfg.edges = b.cfg.edges := rfl

@[simp] lemma emitEdge_nodes (s d : BigNodeID) (k : EdgeKind) (b : BigCFGBuilder) :
    ((BigCFGBuilder.emitEdge s d k).run b).2.cfg.nodes = b.cfg.nodes := rfl

@[simp] lemma emitEdge_edges (s d : BigNodeID) (k : EdgeKind) (b : BigCFGBuilder) :
    ((BigCFGBuilder.emitEdge s d k).run b).2.cfg.edges = b.cfg.edges ++ [⟨s, d, k⟩] := rfl

def buildExpr : Expr -> BuilderM (BigNodeID × BigNodeID)
| .Var x => do
    let en <- freshNode (.EEntry (.Var x))
    let ex <- freshNode (.EExit)
    emitEdge en ex .Normal
    return (en, ex)
| .Int n => do
    let en <- freshNode (.EEntry (.Int n))
    let ex <- freshNode (.EExit)
    emitEdge en ex .Normal
    return (en, ex)
| .BinOp o e₁ e₂ => do
    let en   <- freshNode (.EEntry (.BinOp o e₁ e₂))
    let (en₁, ex₁) <- buildExpr e₁
    let (en₂, ex₂) <- buildExpr e₂
    let ex   <- freshNode .EExit
    emitEdge en  en₁ .Normal
    emitEdge ex₁ en₂ .Normal
    emitEdge ex₂ ex  .Normal
    return (en, ex)

def assignGraph (x : String) (e : Expr) : BuilderM (BigNodeID × BigNodeID) := do
  let en <- freshNode (.SEntry (.Assign x e))
  let (een, eex) <- buildExpr e
  let ex <- freshNode .SExit
  emitEdge en een .Normal
  emitEdge eex ex .Normal
  return (en, ex)

def declGraph (x : String) (e : Expr) : BuilderM (BigNodeID × BigNodeID) := do
  let en <- freshNode (.SEntry (.Decl x e))
  let (een, eex) <- buildExpr e
  let ex <- freshNode .SExit
  emitEdge en een .Normal
  emitEdge eex ex .Normal
  return (en, ex)

def buildStmt : Stmt -> BuilderM (BigNodeID × BigNodeID)
| .Skip => do
    let en <- freshNode (.SEntry .Skip)
    return (en, en)
| .Assign x e => do
    let en <- freshNode (.SEntry (.Assign x e))
    let (een, eex) <- buildExpr e
    let ex <- freshNode .SExit
    emitEdge en een .Normal
    emitEdge eex ex .Normal
    return (en, ex)
| .Decl x e => do
    let en <- freshNode (.SEntry (.Decl x e))
    let (een, eex) <- buildExpr e
    let ex <- freshNode .SExit
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

namespace Spec

def BuilderInv (b : BigCFGBuilder) : Prop := ∀ e ∈ b.cfg.edges,
  e.src < b.cfg.nodes.length ∧ e.dst < b.cfg.nodes.length

lemma BuilderInv.empty : BuilderInv (BigCFGBuilder.empty) := by
  intros e he
  cases he

structure BuildSpec (pre : BigCFGBuilder) (en ex : BigNodeID)
    (post : BigCFGBuilder) : Prop where
  nodes_prefix  : pre.cfg.nodes = post.cfg.nodes.take pre.cfg.nodes.length
  edges_prefix  : pre.cfg.edges = post.cfg.edges.take pre.cfg.edges.length
  en_is_fresh   : en = pre.cfg.nodes.length
  ex_in_range   : pre.cfg.nodes.length ≤ ex ∧ ex < post.cfg.nodes.length
  edges_valid   : ∀ e ∈ post.cfg.edges,
                    e.src < post.cfg.nodes.length ∧
                    e.dst < post.cfg.nodes.length
  en_no_pred    : ∀ e ∈ post.cfg.edges, e.dst ≠ en
  ex_no_succ    : ∀ e ∈ post.cfg.edges, e.src ≠ ex
  edges_dst_lo  : ∀ e ∈ post.cfg.edges, e ∉ pre.cfg.edges ->
                    pre.cfg.nodes.length < e.dst

theorem BuildSpec.trans {p₁ p₂ p₃ : BigCFGBuilder} {en₁ en₂ ex₁ ex₂}
    (h₁ : BuildSpec p₁ en₁ ex₂ p₂) (h₂ : BuildSpec p₂ en₂ ex₂ p₃) :
    BuildSpec p₁ en₁ ex₁ p₂ := by
  grind [BuildSpec]

lemma BuilderInv.expr_pres (pre : BigCFGBuilder) (hpre : BuilderInv pre) (e : Expr) :
    let ((en, ex), post) := ((BigCFGBuilder.buildExpr e)).run pre
    BuilderInv post ∧ BuildSpec pre en ex post := by
  induction e generalizing pre with
  | Int n =>
    refine ⟨?_, ?_⟩
    · intros e he
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at *
      cases he <;> grind [BuilderInv]
    · constructor <;>
        first
        | grind [BuilderInv]
        | simp
  | Var x =>
    refine ⟨?_, ?_⟩
    · simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
        List.length_cons, List.length_nil, Nat.zero_add]
      intros e he
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.length_append,
        List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at *
      cases he <;> grind [BuilderInv]
    · constructor <;>
        first
        | grind [BuilderInv]
        | simp
  | BinOp o e₁ e₂ ih₁ ih₂ =>
    simp only [BigCFGBuilder.buildExpr, bind_pure_comp, StateT.run_bind, StateT.run_map,
      BigCFGBuilder.freshNode_fst]
    set p₁ := (StateT.run (BigCFGBuilder.freshNode (BigNodeKind.EEntry
        (Expr.BinOp o e₁ e₂))) pre).snd
    have hinv₁ : BuilderInv p₁ := by
      simp only [BuilderInv, BigCFGBuilder.freshNode_edges, BigCFGBuilder.freshNode_nodes,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add, p₁]
      intros e he
      grind [BuilderInv]
    specialize ih₁ p₁ hinv₁
    split at ih₁
    case h_1 _ en₁ ex₁ post₁ h₁ =>
    set p₂ := (StateT.run (BigCFGBuilder.buildExpr e₁) p₁).snd
    have hinv₂ : BuilderInv p₂ := by
      simp only [BuilderInv, p₂]
      intros e he
      grind [BuilderInv]
    specialize ih₂ p₂ hinv₂
    split at ih₂
    case h_1 _ en₂ ex₂ post₂ h₂ =>
    have hp1_nodes : p₁.cfg.nodes.length = pre.cfg.nodes.length + 1 := by
      simp [p₁, BigCFGBuilder.freshNode_nodes]
    have hp1_edges : p₁.cfg.edges = pre.cfg.edges := by simp [p₁]
    obtain ⟨hp₁, hs₁⟩ := ih₁
    obtain ⟨hp₂, hs₂⟩ := ih₂
    simp only [h₂, h₁]
    refine ⟨?_, ?_⟩
    · intros e he
      simp only [BigCFGBuilder.emitEdge_edges, BigCFGBuilder.freshNode_edges, List.append_assoc,
        List.cons_append, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at he
      simp only [BigCFGBuilder.freshNode, bind_pure_comp, StateT.run_bind, StateT.run_get,
        StateT.run_map, StateT.run_set, map_pure, BigCFGBuilder.emitEdge_nodes]
      simp only [pure]
      rcases he with h|h|h|h|h <;> grind [BuildSpec]
    · have : pre.cfg.nodes <+: post₂.cfg.nodes := by
        grind [List.prefix_append, BigCFGBuilder.freshNode_nodes, BuildSpec]
      have : pre.cfg.nodes = post₂.cfg.nodes.take pre.cfg.nodes.length :=
        List.prefix_iff_eq_take.mp this
      have : pre.cfg.edges <+: post₂.cfg.edges := by
        grind [List.prefix_append, BigCFGBuilder.freshNode_edges, BuildSpec]
      have : pre.cfg.edges = post₂.cfg.edges.take pre.cfg.edges.length :=
        List.prefix_iff_eq_take.mp this
      constructor
      · simp only [BigCFGBuilder.emitEdge_nodes, BigCFGBuilder.freshNode_nodes]
        grind [List.prefix_iff_eq_take, List.IsPrefix.trans, List.prefix_append]
      · simp only [BigCFGBuilder.emitEdge_edges, BigCFGBuilder.freshNode_edges,
          List.append_assoc, List.cons_append, List.nil_append]
        apply List.prefix_iff_eq_take.mp ?_
        apply List.IsPrefix.trans (by assumption) (List.prefix_append _ _)
      · rfl
      · simp only [BigCFGBuilder.emitEdge_nodes, BigCFGBuilder.freshNode_nodes]
        grind [List.prefix_iff_eq_take, List.IsPrefix.trans, List.prefix_append]
      · simp only [BigCFGBuilder.emitEdge_nodes, BigCFGBuilder.freshNode_nodes]
        intros e he
        simp only [BigCFGBuilder.emitEdge_edges, BigCFGBuilder.freshNode_edges,
          List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with h|h|h|h
        · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
          grind [BuilderInv]
        all_goals
          simp [h]
          grind [BuildSpec]
      · simp only [BigCFGBuilder.emitEdge_edges, BigCFGBuilder.freshNode_edges,
          List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false, ne_eq]
        intros e he hc
        rcases he with h|h|h|h
        · by_cases h' : e ∈ pre.cfg.edges
          · grind [BuilderInv]
          · grind [BuildSpec]
        all_goals grind [BuildSpec]
      · simp only [BigCFGBuilder.emitEdge_edges, BigCFGBuilder.freshNode_edges,
          List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false, ne_eq]
        intros e he hc
        rcases he with h|h|h|h <;> grind [BuildSpec]
      · simp only [BigCFGBuilder.emitEdge_edges, BigCFGBuilder.freshNode_edges,
          List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false]
        intros e he hn
        have hr : e ∉ p₁.cfg.edges := by simpa [p₁]
        rcases he with h|h|h|h <;> grind [BuildSpec]

lemma BuilderInv.stmt_pres (pre : BigCFGBuilder) (hpre : BuilderInv pre) (s : Stmt) :
    let ((en, ex), post) :=  ((BigCFGBuilder.buildStmt s)).run pre
    BuilderInv post ∧ BuildSpec pre en ex post := by
  induction s generalizing pre with
  | Skip =>
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at *
      grind [BuilderInv]
    · constructor <;>
      first
      | grind [BuilderInv]
      | simp
  | Assign x e
  | Decl x e =>
    have ⟨he₁, he₂⟩ := BuilderInv.expr_pres pre hpre e
    set eg := (BigCFGBuilder.buildExpr e)
    refine ⟨?_, ?_⟩
    · intros e' he'
      simp only [List.append_assoc, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at he'
      simp only [List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add]
      sorry
    · sorry
  | Seq s₁ s₂ ih₁ ih₂ =>
    sorry
  | If c t e iht ihe =>
    obtain ⟨l, r⟩ := BuilderInv.expr_pres pre hpre c
    set res := BigCFGBuilder.buildExpr c pre
    refine ⟨?_, ?_⟩
    · sorry
    · sorry
  | While c b ihb =>
    sorry
end Spec

namespace BigCFG

def WellFormed (g : BigCFG) : Prop :=
  g.entry ≤ g.nodes.length ∧
  (∀ e ∈ g.edges, e.src < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.dst < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.dst ≠ g.entry)

def empty_WF : BigCFGBuilder.empty.cfg.WellFormed := by
  simp [BigCFGBuilder.empty, BigCFG.WellFormed]

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

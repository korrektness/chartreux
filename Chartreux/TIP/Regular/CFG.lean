import Chartreux.TIP.Defs
import Chartreux.Analysis.Utils
import Mathlib.Tactic.Lemma
import Mathlib.Data.List.Nodup

inductive NodeKind where
| Assign (x : String) (e : Expr)
| Decl (x : String) (e : Expr)
| Cond (c : Expr)
| Skip
deriving DecidableEq, Repr

abbrev NodeID := Nat

inductive EdgeKind where
| Normal
| TBranch
| FBranch
deriving DecidableEq, Repr

structure Edge where
  src : NodeID
  dst : NodeID
  kind : EdgeKind
deriving DecidableEq, Repr

structure CFG where
  nodes : List NodeKind
  edges : List Edge
  entry : Nat
  exit : Nat

namespace CFG
def nodeKind (g : CFG) (n : NodeID) : Option NodeKind :=
  g.nodes[n]?
def hasEdge (g : CFG) (src dst : NodeID) (k : EdgeKind) : Prop :=
  ⟨src, dst, k⟩ ∈ g.edges
end CFG

-- could the builder carry invariants about the current CFG shape and
-- edges formation, to avoid rebuilding over and over again?
structure CFGBuilder where
  cfg : CFG
  nextID : NodeID

namespace CFGBuilder
def empty : CFGBuilder := {
  cfg := ⟨[], [], 0, 0⟩
  nextID := 0
}

def addNode (b : CFGBuilder) (k : NodeKind) : (CFGBuilder × NodeID) := ({
  cfg := { b.cfg with nodes := b.cfg.nodes ++ [k] }
  nextID := b.nextID + 1
}, b.nextID)

def addEdge (b : CFGBuilder) (s d : NodeID) (k : EdgeKind) : CFGBuilder := {
  b with cfg := { b.cfg with edges := b.cfg.edges ++ [⟨s, d, k⟩] }
}

/-!
# `BuildSpec` — structural witness of the CFG builder

From builder `b`, recursing into statement `s`, you obtain `b'` such that
result is well-formed.
-/

/-- Well-formedness for a builder: the next-fresh node id agrees with
    the current node count. The empty builder is well-formed and both
    `addNode` and `addEdge` preserve this invariant. -/
def BuilderInv (b : CFGBuilder) : Prop :=
  b.nextID = b.cfg.nodes.length

namespace BuilderInv

@[simp] lemma empty : BuilderInv CFGBuilder.empty := by
  simp [BuilderInv, CFGBuilder.empty]

lemma addNode {b} (h : BuilderInv b) (k : NodeKind) :
    BuilderInv (b.addNode k).fst := by
  simpa [BuilderInv, CFGBuilder.addNode] using h

lemma addEdge {b} (h : BuilderInv b) (s d : NodeID) (ek : EdgeKind) :
    BuilderInv (b.addEdge s d ek) := by
  simpa [BuilderInv, CFGBuilder.addEdge] using h

end BuilderInv

/-! ## `BuildSpec` -/

/-- Witness that `⟨b, s⟩ -> b'` -/
inductive BuildSpec :
    CFGBuilder -> Stmt -> CFGBuilder -> NodeID -> NodeID -> Prop where
| skip (b : CFGBuilder) :
    BuildSpec b .Skip (b.addNode .Skip).fst b.nextID b.nextID
| assign (b : CFGBuilder) (x : String) (e : Expr) :
    BuildSpec b (.Assign x e)
      (((b.addNode (.Assign x e)).fst.addNode .Skip).fst.addEdge
        b.nextID (b.nextID + 1) .Normal)
      b.nextID (b.nextID + 1)
| decl (b : CFGBuilder) (x : String) (e : Expr) :
    BuildSpec b (.Decl x e)
      (((b.addNode (.Decl x e)).fst.addNode .Skip).fst.addEdge
        b.nextID (b.nextID + 1) .Normal)
      b.nextID (b.nextID + 1)
| seq {b b₁ b₂ : CFGBuilder} {s₁ s₂ : Stmt}
    {en₁ ex₁ en₂ ex₂ : NodeID} :
    BuildSpec b s₁ b₁ en₁ ex₁ ->
    BuildSpec b₁ s₂ b₂ en₂ ex₂ ->
    BuildSpec b (.Seq s₁ s₂) (b₂.addEdge ex₁ en₂ .Normal) en₁ ex₂
| if_ {b b₁ b₂ : CFGBuilder} {c : Expr} {t f : Stmt}
    {en_t ex_t en_f ex_f : NodeID} :
    BuildSpec (b.addNode (.Cond c)).fst t b₁ en_t ex_t ->
    BuildSpec b₁ f b₂ en_f ex_f ->
    BuildSpec b (.If c t f)
      (let b₃ := (b₂.addNode .Skip).fst
        let nenc := b.nextID
        let nexit := b₂.nextID
        (((b₃.addEdge nenc en_t .TBranch).addEdge nenc en_f .FBranch).addEdge
            ex_t nexit .Normal).addEdge ex_f nexit .Normal)
      b.nextID b₂.nextID
| while_ {b b₁ : CFGBuilder} {c : Expr} {body : Stmt}
    {en_b ex_b : NodeID} :
    BuildSpec (b.addNode (.Cond c)).fst body b₁ en_b ex_b ->
    BuildSpec b (.While c body)
      (let b₂ := (b₁.addNode .Skip).fst
        let nenc := b.nextID
        let nex := b₁.nextID
        ((b₂.addEdge nenc en_b .TBranch).addEdge ex_b nenc .Normal).addEdge
          nenc nex .FBranch)
      b.nextID b₁.nextID

namespace BuildSpec

@[simp] lemma addNode_nodes (b : CFGBuilder) (k : NodeKind) :
    (b.addNode k).fst.cfg.nodes = b.cfg.nodes ++ [k] := rfl

@[simp] lemma addNode_edges (b : CFGBuilder) (k : NodeKind) :
    (b.addNode k).fst.cfg.edges = b.cfg.edges := rfl

@[simp] lemma addNode_nextID (b : CFGBuilder) (k : NodeKind) :
    (b.addNode k).fst.nextID = b.nextID + 1 := rfl

@[simp] lemma addEdge_nodes (b : CFGBuilder) (s d : NodeID) (k : EdgeKind) :
    (b.addEdge s d k).cfg.nodes = b.cfg.nodes := rfl

@[simp] lemma addEdge_edges (b : CFGBuilder) (s d : NodeID) (k : EdgeKind) :
    (b.addEdge s d k).cfg.edges = b.cfg.edges ++ [⟨s, d, k⟩] := rfl

@[simp] lemma addEdge_nextID (b : CFGBuilder) (s d : NodeID) (k : EdgeKind) :
    (b.addEdge s d k).nextID = b.nextID := rfl

theorem preserves_WF {b s b' en ex} (hbs : BuildSpec b s b' en ex)
    (hwf : BuilderInv b) : BuilderInv b' := by
  induction hbs with
  | skip b
  | assign b x e
  | decl b x e =>
    grind [BuilderInv.addEdge, BuilderInv.addNode]
  | seq _ _ ih₁ ih₂ =>
    have h₁ := ih₁ hwf
    have h₂ := ih₂ h₁
    exact BuilderInv.addEdge h₂ _ _ _
  | if_ _ _ ih_t ih_f =>
    case if_ _ _ c _ _ _ _ _ _ _ _ =>
    have h_cond := BuilderInv.addNode hwf (.Cond c)
    have h_t := ih_t h_cond
    have h_f := ih_f h_t
    have h_skip := BuilderInv.addNode h_f .Skip
    repeat (apply BuilderInv.addEdge); exact h_skip
  | while_ _ ih_b =>
    case while_ _ _ c _ _ _ _ =>
    have h_cond := BuilderInv.addNode hwf (.Cond c)
    have h_b := ih_b h_cond
    have h_skip := BuilderInv.addNode h_b .Skip
    repeat (apply BuilderInv.addEdge); exact h_skip

theorem nodes_prefix {b s b' en ex} (hbs : BuildSpec b s b' en ex) :
    ∃ ns, b'.cfg.nodes = b.cfg.nodes ++ ns := by
  induction hbs with
  | skip b => exact ⟨[.Skip], rfl⟩
  | assign b x e => exact ⟨[.Assign x e, .Skip], by simp⟩
  | decl b x e => exact ⟨[.Decl x e, .Skip], by simp⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨ns₁, h₁⟩ := ih₁
    obtain ⟨ns₂, h₂⟩ := ih₂
    refine ⟨ns₁ ++ ns₂, ?_⟩
    simp [addEdge_nodes, h₂, h₁, List.append_assoc]
  | if_ _ _ ih_t ih_f =>
    case if_ _ _ c _ _ _ _ _ _ _ _ =>
    obtain ⟨ns_t, h_t⟩ := ih_t
    obtain ⟨ns_f, h_f⟩ := ih_f
    refine ⟨[.Cond c] ++ ns_t ++ ns_f ++ [.Skip], ?_⟩
    simp only [addEdge_nodes, addNode_nodes, h_f, h_t]
    simp [List.append_assoc]
  | while_ _ ih_b =>
    case while_ _ _ c _ _ _ _ =>
    obtain ⟨ns_b, h_b⟩ := ih_b
    refine ⟨[.Cond c] ++ ns_b ++ [.Skip], ?_⟩
    simp only [addEdge_nodes, addNode_nodes, h_b]
    simp [List.append_assoc]

theorem edges_sublist {b s b' en ex} (hbs : BuildSpec b s b' en ex) :
    ∃ es, b'.cfg.edges = b.cfg.edges ++ es := by
  induction hbs with
  | skip b => exact ⟨[], by simp⟩
  | assign b x e => exact ⟨[⟨b.nextID, b.nextID + 1, .Normal⟩], by simp⟩
  | decl b x e => exact ⟨[⟨b.nextID, b.nextID + 1, .Normal⟩], by simp⟩
  | seq _ _ ih₁ ih₂ =>
    case seq b b₁ b₂ s₁ s₂ en₁ ex₁ en₂ ex₂ _ _ =>
    obtain ⟨es₁, h₁⟩ := ih₁
    obtain ⟨es₂, h₂⟩ := ih₂
    refine ⟨es₁ ++ es₂ ++ [⟨ex₁, en₂, .Normal⟩], ?_⟩
    simp [addEdge_edges, h₂, h₁, List.append_assoc]
  | @if_ b b₁ b₂ c t f en_t ex_t en_f ex_f _ _ ih_t ih_f =>
    obtain ⟨es_t, h_t⟩ := ih_t
    obtain ⟨es_f, h_f⟩ := ih_f
    refine ⟨es_t ++ es_f ++ [⟨b.nextID, en_t, .TBranch⟩, ⟨b.nextID, en_f, .FBranch⟩,
              ⟨ex_t, b₂.nextID, .Normal⟩, ⟨ex_f, b₂.nextID, .Normal⟩], ?_⟩
    simp only [addEdge_edges, addNode_edges, h_f, h_t]
    simp [List.append_assoc]
  | @while_ b b₁ c body en_b ex_b _ ih_b =>
    obtain ⟨es_b, h_b⟩ := ih_b
    refine ⟨es_b ++ [⟨b.nextID, en_b, .TBranch⟩, ⟨ex_b, b.nextID, .Normal⟩,
              ⟨b.nextID, b₁.nextID, .FBranch⟩], ?_⟩
    simp only [addEdge_edges, addNode_edges, h_b]
    simp [List.append_assoc]

/-- Monotonicity: any node id valid in `b` is valid in `b'`. -/
theorem nodes_length_le {b s b' en ex} (hbs : BuildSpec b s b' en ex) :
    b.cfg.nodes.length ≤ b'.cfg.nodes.length := by
  obtain ⟨ns, h⟩ := nodes_prefix hbs
  simp [h]

/-- The kind of any pre-existing node is preserved by the build. -/
theorem preserves_nodeKind {b s b' en ex} (hbs : BuildSpec b s b' en ex)
    {n : NodeID} (hn : n < b.cfg.nodes.length) :
    b'.cfg.nodeKind n = b.cfg.nodeKind n := by
  obtain ⟨ns, h⟩ := nodes_prefix hbs
  simp [CFG.nodeKind, h, List.getElem?_append_left, hn]

/-- Any pre-existing edge survives the build. -/
theorem preserves_edge {b s b' en ex} (hbs : BuildSpec b s b' en ex)
    {e : Edge} (he : e ∈ b.cfg.edges) : e ∈ b'.cfg.edges := by
  obtain ⟨es, h⟩ := edges_sublist hbs
  simp [h, he]

theorem preserves_hasEdge {b s b' en ex} (hbs : BuildSpec b s b' en ex)
    {src dst : NodeID} {k : EdgeKind} (he : b.cfg.hasEdge src dst k) :
    b'.cfg.hasEdge src dst k :=
  preserves_edge hbs he

/-! ## Bounds on entry / exit node ids -/

theorem entry_lt {b s b' en ex} (hbs : BuildSpec b s b' en ex)
    (hwf : BuilderInv b) : en < b'.cfg.nodes.length := by
  induction hbs with
  | skip b => grind [addNode_nodes, BuilderInv]
  | assign b x e
  | decl b x e =>
    simp [BuilderInv] at hwf
    simp [addEdge_nodes, addNode_nodes, hwf]
  | @seq b b₁ b₂ s₁ s₂ en₁ ex₁ en₂ ex₂ _ _ ih₁ _ =>
    have := ih₁ hwf
    obtain ⟨es, h⟩ := edges_sublist (s := s₂) (by assumption)
    have hle : b₁.cfg.nodes.length ≤ b₂.cfg.nodes.length :=
      nodes_length_le (by assumption)
    grind [addEdge_nodes]
  | @if_ b b₁ b₂ c t f en_t ex_t en_f ex_f _ _ ih_t _ =>
    -- en = b.nextID = b.cfg.nodes.length; b' adds Cond, t, f, Skip, edges
    simp [addEdge_nodes, addNode_nodes, BuilderInv] at hwf ⊢
    have hle₁ : (b.addNode (.Cond c)).fst.cfg.nodes.length ≤ b₁.cfg.nodes.length :=
      nodes_length_le (by assumption)
    have hle₂ : b₁.cfg.nodes.length ≤ b₂.cfg.nodes.length :=
      nodes_length_le (by assumption)
    simp [addNode_nodes] at hle₁
    grind
  | @while_ b b₁ c body en_b ex_b _ _ =>
    simp [addEdge_nodes, addNode_nodes, BuilderInv] at hwf ⊢
    have hle₁ : (b.addNode (.Cond c)).fst.cfg.nodes.length ≤ b₁.cfg.nodes.length :=
      nodes_length_le (by assumption)
    simp [addNode_nodes] at hle₁
    grind

theorem exit_lt {b s b' en ex} (hbs : BuildSpec b s b' en ex)
    (hwf : BuilderInv b) : ex < b'.cfg.nodes.length := by
  induction hbs with
  | skip b => grind [addNode_nodes, BuilderInv]
  | assign b x e
  | decl b x e =>
    simp [BuilderInv] at hwf
    simp [addEdge_nodes, addNode_nodes, hwf]
  | @seq b b₁ b₂ s₁ s₂ en₁ ex₁ en₂ ex₂ hbs₁ _ _ ih₂ =>
    have hwf₁ := preserves_WF hbs₁ hwf
    have := ih₂ hwf₁
    grind [addEdge_nodes]
  | @if_ b b₁ b₂ c t f en_t ex_t en_f ex_f _ _ _ _ =>
    -- ex = b₂.nextID = b₂.cfg.nodes.length (BuilderInv b₂)
    simp only [BuilderInv, addEdge_nodes, addNode_nodes, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add] at hwf ⊢
    have h_cond : BuilderInv (b.addNode (.Cond c)).fst := BuilderInv.addNode hwf _
    have h_t : BuilderInv b₁ := preserves_WF (by assumption) h_cond
    have h_f : BuilderInv b₂ := preserves_WF (by assumption) h_t
    rw [BuilderInv] at h_f
    grind
  | @while_ b b₁ c body en_b ex_b hbs_b _ =>
    -- ex = b₁.nextID = b₁.cfg.nodes.length
    simp only [BuilderInv, addEdge_nodes, addNode_nodes, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add] at hwf ⊢
    have h_cond : BuilderInv (b.addNode (.Cond c)).fst := BuilderInv.addNode hwf _
    have h_b : BuilderInv b₁ := preserves_WF hbs_b h_cond
    rw [BuilderInv] at h_b
    grind

/-! ## Per-constructor edge witnesses -/

theorem seq_normal_edge {b b₁ b₂ : CFGBuilder} {s₁ s₂ : Stmt}
    {en₁ ex₁ en₂ ex₂ : NodeID}
    (_ : BuildSpec b s₁ b₁ en₁ ex₁) (_ : BuildSpec b₁ s₂ b₂ en₂ ex₂) :
    (b₂.addEdge ex₁ en₂ .Normal).cfg.hasEdge ex₁ en₂ .Normal := by
  simp [CFG.hasEdge, addEdge_edges]

theorem if_edges {b b₁ b₂ : CFGBuilder} {c : Expr} {t f : Stmt}
    {en_t ex_t en_f ex_f : NodeID}
    (_hbs_t : BuildSpec (b.addNode (.Cond c)).fst t b₁ en_t ex_t)
    (_hbs_f : BuildSpec b₁ f b₂ en_f ex_f) :
    let b₃ := (b₂.addNode .Skip).fst
    let g  := ((((b₃.addEdge b.nextID en_t .TBranch).addEdge
      b.nextID en_f .FBranch).addEdge ex_t b₂.nextID .Normal).addEdge
        ex_f b₂.nextID .Normal).cfg
    g.hasEdge b.nextID en_t .TBranch ∧
    g.hasEdge b.nextID en_f .FBranch ∧
    g.hasEdge ex_t b₂.nextID .Normal ∧
    g.hasEdge ex_f b₂.nextID .Normal := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [CFG.hasEdge]

theorem while_edges {b b₁ : CFGBuilder} {c : Expr} {body : Stmt}
    {en_b ex_b : NodeID}
    (_hbs_b : BuildSpec (b.addNode (.Cond c)).fst body b₁ en_b ex_b) :
    let b₂ := (b₁.addNode .Skip).fst
    let g  := (((b₂.addEdge b.nextID en_b .TBranch).addEdge
      ex_b b.nextID .Normal).addEdge b.nextID b₁.nextID .FBranch).cfg
    g.hasEdge b.nextID en_b .TBranch ∧
    g.hasEdge ex_b b.nextID .Normal ∧
    g.hasEdge b.nextID b₁.nextID .FBranch := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [CFG.hasEdge]

/-! ## Per-constructor node-kind witnesses -/

private lemma addNode_nodeKind (b : CFGBuilder) (k : NodeKind) (hwf : BuilderInv b) :
    (b.addNode k).fst.cfg.nodeKind b.nextID = some k := by
  rw [hwf]
  simp [CFGBuilder.addNode, CFG.nodeKind]

theorem skip_nodeKind (b : CFGBuilder) (hwf : BuilderInv b) :
    (b.addNode .Skip).fst.cfg.nodeKind b.nextID = some .Skip :=
  addNode_nodeKind b .Skip hwf

theorem assign_nodeKind (b : CFGBuilder) (x : String) (e : Expr) (hwf : BuilderInv b) :
    (b.addNode (.Assign x e)).fst.cfg.nodeKind b.nextID = some (.Assign x e) :=
  addNode_nodeKind b (.Assign x e) hwf

theorem decl_nodeKind (b : CFGBuilder) (x : String) (e : Expr) (hwf : BuilderInv b) :
    (b.addNode (.Decl x e)).fst.cfg.nodeKind b.nextID = some (.Decl x e) :=
  addNode_nodeKind b (.Decl x e) hwf

/-! ## Witnesses for the trailing `Skip` and `Normal` edge -/

theorem assign_kind_at_entry {b : CFGBuilder} (x : String) (e : Expr)
    (hwf : BuilderInv b) :
    let b' := (((b.addNode (.Assign x e)).fst.addNode .Skip).fst.addEdge
                  b.nextID (b.nextID + 1) .Normal)
    b'.cfg.nodeKind b.nextID = some (.Assign x e) := by
  simp only [CFG.nodeKind, addEdge_nodes, addNode_nodes,
             List.append_assoc, List.cons_append, List.nil_append]
  rw [hwf]
  simp

theorem decl_kind_at_entry {b : CFGBuilder} (x : String) (e : Expr)
    (hwf : BuilderInv b) :
    let b' := (((b.addNode (.Decl x e)).fst.addNode .Skip).fst.addEdge
                  b.nextID (b.nextID + 1) .Normal)
    b'.cfg.nodeKind b.nextID = some (.Decl x e) := by
  simp only [CFG.nodeKind, addEdge_nodes, addNode_nodes,
             List.append_assoc, List.cons_append, List.nil_append]
  rw [hwf]
  simp

theorem assign_skip_kind_at_exit {b : CFGBuilder} (x : String) (e : Expr)
    (hwf : BuilderInv b) :
    let b' := (((b.addNode (.Assign x e)).fst.addNode .Skip).fst.addEdge
                  b.nextID (b.nextID + 1) .Normal)
    b'.cfg.nodeKind (b.nextID + 1) = some .Skip := by
  simp only [CFG.nodeKind, addEdge_nodes, addNode_nodes,
             List.append_assoc, List.cons_append, List.nil_append]
  rw [hwf]
  simp

theorem decl_skip_kind_at_exit {b : CFGBuilder} (x : String) (e : Expr)
    (hwf : BuilderInv b) :
    let b' := (((b.addNode (.Decl x e)).fst.addNode .Skip).fst.addEdge
                  b.nextID (b.nextID + 1) .Normal)
    b'.cfg.nodeKind (b.nextID + 1) = some .Skip := by
  simp only [CFG.nodeKind, addEdge_nodes, addNode_nodes,
             List.append_assoc, List.cons_append, List.nil_append]
  rw [hwf]
  simp

theorem assign_normal_edge {b : CFGBuilder} (x : String) (e : Expr) :
    let b' := (((b.addNode (.Assign x e)).fst.addNode .Skip).fst.addEdge
                  b.nextID (b.nextID + 1) .Normal)
    b'.cfg.hasEdge b.nextID (b.nextID + 1) .Normal := by
  simp [CFG.hasEdge]

theorem decl_normal_edge {b : CFGBuilder} (x : String) (e : Expr) :
    let b' := (((b.addNode (.Decl x e)).fst.addNode .Skip).fst.addEdge
                  b.nextID (b.nextID + 1) .Normal)
    b'.cfg.hasEdge b.nextID (b.nextID + 1) .Normal := by
  simp [CFG.hasEdge]

theorem exit_nodeKind_skip {b s b' en ex} (hbs : BuildSpec b s b' en ex)
    (hwf : BuilderInv b) : b'.cfg.nodeKind ex = some .Skip := by
  induction hbs with
  | skip b => exact skip_nodeKind b hwf
  | assign b x e => exact assign_skip_kind_at_exit x e hwf
  | decl b x e => exact decl_skip_kind_at_exit x e hwf
  | @seq b b₁ b₂ s₁ s₂ en₁ ex₁ en₂ ex₂ hbs₁ hbs₂ _ ih₂ =>
    have hwf₁ := preserves_WF hbs₁ hwf
    have h_ex₂ : b₂.cfg.nodeKind ex₂ = some .Skip := ih₂ hwf₁
    have h_ex₂_lt : ex₂ < b₂.cfg.nodes.length := exit_lt hbs₂ hwf₁
    simpa [CFG.nodeKind, h_ex₂_lt, getElem?_pos, Option.some.injEq,
      addEdge_nodes] using h_ex₂
  | @if_ b b₁ b₂ c t f en_t ex_t en_f ex_f _ _ _ _ =>
    have h_b₂_wf : BuilderInv b₂ := by
      have h_cond : BuilderInv (b.addNode (.Cond c)).fst := BuilderInv.addNode hwf _
      exact preserves_WF (by assumption) (preserves_WF (by assumption) h_cond)
    rw [BuilderInv] at h_b₂_wf
    simp [CFG.nodeKind, addEdge_nodes, addNode_nodes, h_b₂_wf]
  | @while_ b b₁ c body en_b ex_b _ _ =>
    have h_b₁_wf : BuilderInv b₁ := by
      have h_cond : BuilderInv (b.addNode (.Cond c)).fst := BuilderInv.addNode hwf _
      exact preserves_WF (by assumption) h_cond
    rw [BuilderInv] at h_b₁_wf
    simp [CFG.nodeKind, addEdge_nodes, addNode_nodes, h_b₁_wf]

end BuildSpec

/-! ## `SubCFG` — `g₁` is a structural prefix/sublist of `g₂` -/
def SubCFG (g₁ g₂ : CFG) : Prop :=
  (∃ ns, g₂.nodes = g₁.nodes ++ ns) ∧
  (∃ es, g₂.edges = g₁.edges ++ es)

namespace SubCFG

theorem refl (g : CFG) : SubCFG g g :=
  ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem trans {g₁ g₂ g₃ : CFG}
    (h₁ : SubCFG g₁ g₂) (h₂ : SubCFG g₂ g₃) : SubCFG g₁ g₃ := by
  obtain ⟨⟨ns₁, hn₁⟩, ⟨es₁, he₁⟩⟩ := h₁
  obtain ⟨⟨ns₂, hn₂⟩, ⟨es₂, he₂⟩⟩ := h₂
  refine ⟨⟨ns₁ ++ ns₂, ?_⟩, ⟨es₁ ++ es₂, ?_⟩⟩
  · simp [hn₂, hn₁, List.append_assoc]
  · simp [he₂, he₁, List.append_assoc]

theorem nodeKind {g₁ g₂ : CFG} (h : SubCFG g₁ g₂) {n : NodeID}
    (hn : n < g₁.nodes.length) : g₂.nodeKind n = g₁.nodeKind n := by
  obtain ⟨⟨ns, hns⟩, _⟩ := h
  simp [CFG.nodeKind, hns, List.getElem?_append_left, hn]

theorem hasEdge {g₁ g₂ : CFG} (h : SubCFG g₁ g₂)
    {src dst : NodeID} {k : EdgeKind} (he : g₁.hasEdge src dst k) :
    g₂.hasEdge src dst k := by
  obtain ⟨_, ⟨es, hes⟩⟩ := h
  simp only [CFG.hasEdge, hes, List.mem_append]
  exact Or.inl he

theorem of_buildSpec {b s b' en ex} (hbs : BuildSpec b s b' en ex) :
    SubCFG b.cfg b'.cfg :=
  ⟨BuildSpec.nodes_prefix hbs, BuildSpec.edges_sublist hbs⟩

theorem of_addNode (b : CFGBuilder) (k : NodeKind) :
    SubCFG b.cfg (b.addNode k).fst.cfg :=
  ⟨⟨[k], by simp⟩, ⟨[], by simp⟩⟩

theorem of_addEdge (b : CFGBuilder) (s d : NodeID) (k : EdgeKind) :
    SubCFG b.cfg (b.addEdge s d k).cfg :=
  ⟨⟨[], by simp⟩, ⟨[⟨s, d, k⟩], by simp⟩⟩

end SubCFG

/-! ## Builders -/
/-- `buildGraphSpec`: `buildGraph` with a paired `BuildSpec` witness -/
def buildGraphSpec (b : CFGBuilder) (s : Stmt) :
    Σ' (b' : CFGBuilder) (en ex : NodeID), BuildSpec b s b' en ex :=
  match s with
  | .Skip =>
      ⟨(b.addNode .Skip).fst, b.nextID, b.nextID, .skip b⟩
  | .Assign x e =>
      ⟨((((b.addNode (.Assign x e)).fst.addNode .Skip).fst.addEdge
            b.nextID (b.nextID + 1) .Normal)),
        b.nextID, b.nextID + 1, .assign b x e⟩
  | .Decl x e =>
      ⟨((((b.addNode (.Decl x e)).fst.addNode .Skip).fst.addEdge
            b.nextID (b.nextID + 1) .Normal)),
        b.nextID, b.nextID + 1, .decl b x e⟩
  | .Seq s₁ s₂ =>
      let r₁ := buildGraphSpec b s₁
      let r₂ := buildGraphSpec r₁.1 s₂
      ⟨r₂.1.addEdge r₁.2.2.1 r₂.2.1 .Normal, r₁.2.1, r₂.2.2.1,
        .seq r₁.2.2.2 r₂.2.2.2⟩
  | .If c t f =>
      let b₀ := (b.addNode (.Cond c)).fst
      let r_t := buildGraphSpec b₀ t
      let r_f := buildGraphSpec r_t.1 f
      let b₃  := (r_f.1.addNode .Skip).fst
      let nenc := b.nextID
      let nexit := r_f.1.nextID
      ⟨(((b₃.addEdge nenc r_t.2.1 .TBranch).addEdge nenc r_f.2.1 .FBranch).addEdge
            r_t.2.2.1 nexit .Normal).addEdge r_f.2.2.1 nexit .Normal,
        nenc, nexit, .if_ r_t.2.2.2 r_f.2.2.2⟩
  | .While c body =>
      let b₀ := (b.addNode (.Cond c)).fst
      let r_b := buildGraphSpec b₀ body
      let b₂ := (r_b.1.addNode .Skip).fst
      let nenc := b.nextID
      let nex := r_b.1.nextID
      ⟨((b₂.addEdge nenc r_b.2.1 .TBranch).addEdge r_b.2.2.1 nenc .Normal).addEdge
          nenc nex .FBranch,
        nenc, nex, .while_ r_b.2.2.2⟩

/-- Compatibility: drop the witness -/
def buildGraphTuple (b : CFGBuilder) (s : Stmt) : CFGBuilder × (NodeID × NodeID) :=
  let r := buildGraphSpec b s
  (r.1, (r.2.1, r.2.2.1))

end CFGBuilder

namespace CFG

def WellFormed (g : CFG) : Prop :=
  g.entry < g.nodes.length ∧
  (∀ e ∈ g.edges, e.src < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.dst < g.nodes.length)

instance (g : CFG) : Decidable g.WellFormed := by
  unfold WellFormed; infer_instance

/-- Build a CFG from a `Stmt` using the empty builder. -/
def ofStmt (s : Stmt) : CFG :=
  let r := CFGBuilder.empty.buildGraphTuple s
  { r.1.cfg with entry := r.2.1, exit := r.2.2 }

/-- All variables appearing in the program (declarations and
    assignments), de-duplicated, with a `Nodup` witness. -/
def vars (g : CFG) : { l : List String // l.Nodup } :=
  let base := g.nodes.filterMap (fun k =>
    match k with
    | .Assign x _ => some x
    | .Decl x _   => some x
    | _           => none)
  ⟨base.eraseDups, Utils.List.eraseDups_nodup base⟩

end CFG

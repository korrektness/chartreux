import Flow.Duke.Defs
import Flow.Duke.Eval
import Flow.Analysis.CFG
import Flow.Analysis.Generic

-- # Defs
abbrev NodeID := Nat

inductive NodeKind where
| Assume (e : Expr)
| Assign (x : String) (e : Expr)
| Skip
deriving DecidableEq, Repr

structure Edge where
  src : NodeID
  dst : NodeID
deriving DecidableEq, Repr

structure CFG where
  nodes : List NodeKind
  edges : List Edge
  entry : NodeID
  exit  : NodeID
deriving DecidableEq, Repr

def CFG.nodeKind (g : CFG) (n : NodeID) : Option NodeKind :=
  g.nodes[n]?

-- # Builder
structure BState where
  cfg : CFG
  nextID : NodeID
abbrev Builder := StateM BState

namespace Builder
def addNode (k : NodeKind) : Builder NodeID := do
  let s <- get
  set { s with
        cfg   := { s.cfg with nodes := s.cfg.nodes ++ [k] }
        nextID := s.nextID + 1 }
  pure s.nextID
def addEdge (src dst : NodeID) : Builder Unit := do
  modify fun s => { s with
    cfg := { s.cfg with edges := s.cfg.edges ++ [⟨src, dst⟩] } }
end Builder

open Builder
def lowerStmt : Stmt -> Builder (NodeID × NodeID)
| .Skip => do
    let n <- addNode (.Skip)
    pure (n, n)
| .Decl x e | .Assign x e => do
    let n <- addNode (.Assign x e)
    pure (n, n)
| .Seq s₁ s₂ => do
    let (en₁, ex₁) <- lowerStmt s₁
    let (en₂, ex₂) <- lowerStmt s₂
    addEdge ex₁ en₂
    pure (en₁, ex₂)
| .If c t f => do
    let en <- addNode (.Skip) -- could probably be something in relation to c
    let atru <- addNode (.Assume c)
    let afls <- addNode (.Assume (.Not c))
    let (ent, ext) <- lowerStmt t
    let (enf, exf) <- lowerStmt f
    let ex <- addNode (.Skip)
    addEdge en atru; addEdge en afls
    addEdge atru ent; addEdge afls enf
    addEdge ext ex; addEdge exf ex
    pure (en, ex)
| .While c b => do
    let en <- addNode (.Skip) -- could probably be something in relation to c
    let atru <- addNode (.Assume c)
    let afls <- addNode (.Assume (.Not c))
    let (enb, exb) <- lowerStmt b
    addEdge en atru; addEdge en afls
    addEdge atru enb
    addEdge exb en
    pure (en, afls)

def Stmt.cfg (s : Stmt) : CFG :=
    let (res, st) := (lowerStmt s).run { cfg := ⟨[], [], 0, 0⟩, nextID := 0 }
    { st.cfg with entry := res.1, exit := res.2 }

@[simp] theorem addNode_run (b : BState) (k : NodeKind) :
    StateT.run (Builder.addNode k) b =
      (b.nextID,
        { cfg := { b.cfg with nodes := b.cfg.nodes ++ [k] },
          nextID := b.nextID + 1 }) := rfl

@[simp] theorem addEdge_run (b : BState) (s d : NodeID) :
    StateT.run (Builder.addEdge s d) b =
      ((), { b with cfg := { b.cfg with edges := b.cfg.edges ++ [⟨s, d⟩] } }) := rfl

-- well-formedness invariants
-- TODO: clean this proof up cause hoooooly cow
theorem lowerStmt_spec (s : Stmt) (b : BState) (hinv : b.nextID = b.cfg.nodes.length) :
    let (res, b') := (lowerStmt s).run b
    b'.nextID = b'.cfg.nodes.length ∧
    (∃ ns, b'.cfg.nodes = b.cfg.nodes ++ ns) ∧
    (∃ es, b'.cfg.edges = b.cfg.edges ++ es ∧
      (∀ e ∈ es, e.src < b'.cfg.nodes.length ∧
        e.dst < b'.cfg.nodes.length) ∧
      (∀ n, b.nextID ≤ n → n < b'.nextID → n ≠ res.2 → ∃ n', ⟨n, n'⟩ ∈ es)) ∧
    res.1 < b'.cfg.nodes.length ∧
    res.2 < b'.cfg.nodes.length := by
  induction s generalizing b with
  | Skip => simp [lowerStmt, Builder.addNode, hinv]; grind -- one fresh node
  | Decl x e | Assign x e => simp [lowerStmt, Builder.addNode, hinv]; grind
  | Seq s₁ s₂ ih₁ ih₂ =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure]
    rcases hr₁ : StateT.run (lowerStmt s₁) b with ⟨⟨en₁, ex₁⟩, b₁⟩
    have h₁ := ih₁ b hinv
    rw [hr₁] at h₁
    simp only at h₁
    obtain ⟨hinv₁, ⟨ns₁, hns₁⟩, ⟨es₁, hes₁, hb₁, hedge₁⟩, hen₁, hex₁⟩ := h₁
    rcases hr₂ : StateT.run (lowerStmt s₂) b₁ with ⟨⟨en₂, ex₂⟩, b₂⟩
    have h₂ := ih₂ b₁ hinv₁
    rw [hr₂] at h₂
    simp only at h₂
    obtain ⟨hinv₂, ⟨ns₂, hns₂⟩, ⟨es₂, hes₂, hb₂, hedge₂⟩, hen₂, hex₂⟩ := h₂
    simp only [addEdge_run]
    have hmono : b₁.cfg.nodes.length ≤ b₂.cfg.nodes.length := by rw [hns₂]; simp
    refine ⟨by simpa using hinv₂, ⟨ns₁ ++ ns₂, by rw [hns₂, hns₁]; simp⟩,
      ⟨es₁ ++ es₂ ++ [⟨ex₁, en₂⟩], by simp [hes₂, hes₁, List.append_assoc], ?_⟩,
      by grind, by simpa using hex₂⟩
    split_ands
    · intro e he
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with (he | he) | he
      · exact ⟨by have := (hb₁ e he).1; simp; grind, by have := (hb₁ e he).2; simp; grind⟩
      · have := hb₂ e he; simpa using this
      · subst he; exact ⟨by simp; grind, by simpa using hen₂⟩
    · grind
  | If c t f ih_t ih_f =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run, addEdge_run]
    have hbt0 : (b.nextID + 1 + 1 + 1) = (b.cfg.nodes ++ [NodeKind.Skip] ++
        [NodeKind.Assume c] ++ [NodeKind.Assume c.Not]).length := by
      simp; grind
    have ht := ih_t
      { cfg := { nodes := b.cfg.nodes ++ [NodeKind.Skip] ++ [NodeKind.Assume c] ++
                    [NodeKind.Assume c.Not],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1 + 1 + 1 } hbt0
    rcases hrt : StateT.run (lowerStmt t)
      { cfg := { nodes := b.cfg.nodes ++ [NodeKind.Skip] ++ [NodeKind.Assume c] ++
                  [NodeKind.Assume c.Not],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1 + 1 + 1 } with ⟨⟨ent, ext⟩, bt⟩
    rw [hrt] at ht
    simp only at ht
    obtain ⟨hinvt, ⟨nst, hnst⟩, ⟨est, hest, hbt, hedt⟩, hent, hext⟩ := ht
    have hf := ih_f bt hinvt
    rcases hrf : StateT.run (lowerStmt f) bt with ⟨⟨enf, exf⟩, bf⟩
    rw [hrf] at hf
    simp only at hf
    obtain ⟨hinvf, ⟨nsf, hnsf⟩, ⟨esf, hesf, hbf, hedf⟩, henf, hexf⟩ := hf
    have hL1 : b.cfg.nodes.length + 3 ≤ bt.cfg.nodes.length := by
      rw [hnst]; grind
    have hL2 : bt.cfg.nodes.length ≤ bf.cfg.nodes.length := by rw [hnsf]; simp
    refine ⟨by simp [hinvf], ?_, ?_, by simp; grind, by simp [hinvf]⟩
    · exact ⟨
        [NodeKind.Skip, NodeKind.Assume c, NodeKind.Assume c.Not] ++ nst ++ nsf ++ [NodeKind.Skip],
        by rw [hnsf, hnst]; simp [List.append_assoc]⟩
    · refine ⟨est ++ esf ++ [⟨b.nextID, b.nextID + 1⟩, ⟨b.nextID, b.nextID + 1 + 1⟩,
        ⟨b.nextID + 1, ent⟩, ⟨b.nextID + 1 + 1, enf⟩, ⟨ext, bf.nextID⟩, ⟨exf, bf.nextID⟩],
        by rw [hesf, hest]; simp [List.append_assoc], ?_⟩
      split_ands
      · intro e he
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with (he | he) | he
        · have := hbt e he; simp; grind
        · have := hbf e he; simp; grind
        · rcases he with h|h|h|h|h|h <;> subst h <;> simp <;> grind
      · intro n hn1 hn2 hn3
        by_cases h0 : n = b.nextID; · grind
        by_cases h1 : n = b.nextID + 1; · grind
        by_cases h2 : n = b.nextID + 2; · grind
        have hn1' : b.nextID + 3 ≤ n := by grind
        by_cases ht_range : n < bt.nextID <;> grind
  | While c body ih_b =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run, addEdge_run]
    have hbb0 : (b.nextID + 1 + 1 + 1) = (b.cfg.nodes ++ [NodeKind.Skip] ++ [NodeKind.Assume c] ++
        [NodeKind.Assume c.Not]).length := by
      simp; grind
    have hb := ih_b
      { cfg := { nodes := b.cfg.nodes ++ [NodeKind.Skip] ++ [NodeKind.Assume c] ++
                    [NodeKind.Assume c.Not],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1 + 1 + 1 } hbb0
    rcases hrb : StateT.run (lowerStmt body)
      { cfg := { nodes := b.cfg.nodes ++ [NodeKind.Skip] ++ [NodeKind.Assume c] ++
                    [NodeKind.Assume c.Not],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1 + 1 + 1 } with ⟨⟨enb, exb⟩, bb⟩
    rw [hrb] at hb
    simp only at hb
    obtain ⟨hinvb, ⟨nsb, hnsb⟩, ⟨esb, hesb, hbb, hedb⟩, henb, hexb⟩ := hb
    have hL1 : b.cfg.nodes.length + 3 ≤ bb.cfg.nodes.length := by
      rw [hnsb]; grind
    refine ⟨by simp [hinvb], ?_, ?_, by simp; grind, by simp; grind⟩
    · exact ⟨[NodeKind.Skip, NodeKind.Assume c, NodeKind.Assume c.Not] ++ nsb,
        by rw [hnsb]; simp [List.append_assoc]⟩
    · refine ⟨esb ++ [⟨b.nextID, b.nextID + 1⟩, ⟨b.nextID, b.nextID + 1 + 1⟩,
        ⟨b.nextID + 1, enb⟩, ⟨exb, b.nextID⟩],
        by rw [hesb]; simp [List.append_assoc], ?_⟩
      split_ands
      · intro e he
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with he | he
        · have := hbb e he; simp; grind
        · rcases he with h|h|h|h <;> subst h <;> simp <;> grind
      · intro n hn1 hn2 hn3
        by_cases h0 : n = b.nextID; · grind
        by_cases h1 : n = b.nextID + 1; · grind
        by_cases h2 : n = b.nextID + 2; · grind
        have hn1' : b.nextID + 3 ≤ n := by grind
        by_cases ht_range : n < bb.nextID <;> grind

def CFG.WellFormed (g : CFG) :=
  (g.entry < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.src < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.dst < g.nodes.length) ∧
  (∀ n < g.nodes.length, n ≠ g.exit → ∃ n', ⟨n, n'⟩ ∈ g.edges)

theorem cfg_WF (s : Stmt) : s.cfg.WellFormed := by
  have hspec := lowerStmt_spec s ⟨⟨[], [], 0, 0⟩, 0⟩ rfl
  unfold Stmt.cfg
  generalize hrun :
    StateT.run (lowerStmt s) {cfg:={nodes:=[], edges:=[], entry:=0, exit:=0 }, nextID:=0}
      = run_res at *
  obtain ⟨hlen, -, ⟨es, hes, hbound, hedge⟩, hen, -⟩ := hspec
  simp only [List.nil_append] at hes
  refine ⟨hen, ?_, ?_, ?_⟩
  · intro e he; exact (hbound e (hes ▸ he)).1
  · intro e he; exact (hbound e (hes ▸ he)).2
  · intro n hn_len hn_exit
    obtain ⟨n', hn'⟩ := hedge n (Nat.zero_le n) (by grind) hn_exit
    exact ⟨n', hes ▸ hn'⟩

abbrev WFCFG := { cfg : CFG // cfg.WellFormed }

def Stmt.wfcfg (s : Stmt) : WFCFG :=
  ⟨s.cfg, cfg_WF s⟩

@[reducible]
def DukeAnalysisCFG (g : CFG) (hg : g.WellFormed) :
    AnalysisCFG NodeID Edge where
  nodes     := List.range g.nodes.length
  edges     := g.edges
  entry     := g.entry
  srcOf e   := e.src
  dstOf e   := e.dst
  srcOf_mem := by
    intros e he
    have hsrc := hg.2.1
    exact List.mem_range.mpr (hsrc e he)
  dstOf_mem := by
    intros e he
    have hdst := hg.2.2.1
    exact List.mem_range.mpr (hdst e he)
  entry_mem := by simpa using hg.1

@[reducible]
def WFCFG.analysis (g : WFCFG) : AnalysisCFG NodeID Edge :=
  DukeAnalysisCFG g g.prop

/-- All variables appearing in the program , de-duplicated, with a `Nodup` witness. -/
def vars (g : CFG) : { l : List String // l.Nodup } :=
  let base := g.nodes.filterMap (fun k =>
  match k with
  | .Assign x _ => some x
  | _           => none)
  ⟨base.eraseDups, Utils.List.eraseDups_nodup base⟩

-- # Semantics

abbrev Config := NodeID × State

inductive Step (g : CFG) : Config -> Config -> Prop where
| skip {n n' σ} :
    g.nodeKind n = some .Skip ->
    ⟨n, n'⟩ ∈ g.edges ->
    Step g ⟨n, σ⟩ ⟨n', σ⟩
| assign {n n' x e v σ} :
    g.nodeKind n = some (.Assign x e) ->
    EvalExpr σ e v ->
    ⟨n, n'⟩ ∈ g.edges ->
    Step g ⟨n, σ⟩ ⟨n', σ.updated x v⟩
| assum {n n' m c σ} :
    g.nodeKind n = some (NodeKind.Assume c) ->
    EvalExpr σ c (.Int m) ->
    m != 0 ->
    ⟨n, n'⟩ ∈ g.edges ->
    Step g ⟨n, σ⟩ ⟨n', σ⟩

open Flow.Analysis.Generic in
instance dukeLangSem (cfg : WFCFG) : LangSem NodeID Edge State cfg.analysis where
  LStep e σ σ' := Step cfg ⟨e.val.src, σ⟩ ⟨e.val.dst, σ'⟩
  LStutter _ σ σ' := σ = σ'

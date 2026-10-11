import Chartreux.FDuke.CFG.Builder
import Chartreux.Analysis.Generic
import Mathlib.Tactic.Contrapose
import Mathlib.Data.List.Nodup

-- temporary
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

@[simp] theorem Stmt.generatedCFG_cfg (Φ : FunEnv) (s : Stmt) :
    (s.generatedCFG Φ).cfg = s.cfg Φ := rfl

@[simp] theorem addNode_run (b : BState) (k : NodeKind) :
    StateT.run (Builder.addNode k) b =
      (b.nextID,
        { cfg := { b.cfg with nodes := b.cfg.nodes ++ [k] },
          nextID := b.nextID + 1, nextLam := b.nextLam,
          callGadgets := b.callGadgets }) := rfl

@[simp] theorem addEdge_run (b : BState) (s d : NodeID) :
    StateT.run (Builder.addEdge s d) b =
      ((), { b with cfg := { b.cfg with edges := b.cfg.edges ++ [⟨s, d, .plain⟩] } }) := rfl

@[simp] theorem addEdges_run (b : BState) (es : List Edge) :
    StateT.run (Builder.addEdges es) b =
      ((), { b with cfg := { b.cfg with edges := b.cfg.edges ++ es } }) := rfl

@[simp] theorem addCallNode_run (b : BState) (f : String) :
    StateT.run (Builder.addCallNode f) b =
      (b.nextID,
        { cfg := { b.cfg with nodes := b.cfg.nodes ++ [NodeKind.Call f b.nextLam] },
          nextID := b.nextID + 1, nextLam := b.nextLam + 1,
          callGadgets := b.callGadgets }) := rfl

@[simp] theorem addCallNodeWithLam_run (b : BState) (f : String) :
    StateT.run (Builder.addCallNodeWithLam f) b =
      ((b.nextID, b.nextLam),
        { cfg := { b.cfg with nodes := b.cfg.nodes ++ [NodeKind.Call f b.nextLam] },
          nextID := b.nextID + 1, nextLam := b.nextLam + 1,
          callGadgets := b.callGadgets }) := rfl

@[simp] theorem addCallGadget_run (b : BState) (site : CallGadget) :
    StateT.run (Builder.addCallGadget site) b =
      ((), { b with
        cfg := { b.cfg with edges := b.cfg.edges ++ site.edges },
        callGadgets := b.callGadgets ++ [site] }) := rfl

theorem Builder.addNode_preserves_callGadgetsValid (b : BState) (k : NodeKind)
    (hvalid : b.CallGadgetsValid) :
    (StateT.run (Builder.addNode k) b).2.CallGadgetsValid := by
  intro site hsite e he
  exact hvalid site hsite he

theorem Builder.addEdge_preserves_callGadgetsValid (b : BState) (src dst : NodeID)
    (hvalid : b.CallGadgetsValid) :
    (StateT.run (Builder.addEdge src dst) b).2.CallGadgetsValid := by
  intro site hsite e he
  exact List.mem_append_left _ (hvalid site hsite he)

theorem Builder.addCallNodeWithLam_preserves_callGadgetsValid (b : BState) (f : String)
    (hvalid : b.CallGadgetsValid) :
    (StateT.run (Builder.addCallNodeWithLam f) b).2.CallGadgetsValid := by
  intro site hsite e he
  exact hvalid site hsite he

theorem Builder.addCallGadget_preserves_callGadgetsValid (b : BState) (site : CallGadget)
    (hvalid : b.CallGadgetsValid) :
    (StateT.run (Builder.addCallGadget site) b).2.CallGadgetsValid := by
  intro other hother e he
  simp only [addCallGadget_run, List.mem_append, List.mem_singleton] at hother ⊢
  rcases hother with hother | rfl
  · exact Or.inl (hvalid other hother he)
  · exact Or.inr he

/-- Atomic gadget emission records the site and inserts every certified edge. -/
theorem Builder.addCallGadget_records_present (b : BState) (site : CallGadget) :
    site ∈ (StateT.run (Builder.addCallGadget site) b).2.callGadgets ∧
    (StateT.run (Builder.addCallGadget site) b).2.cfg.HasKappaGadget
      site.kappa site.en site.enL site.exL site.ret := by
  constructor
  · simp
  · intro e he
    exact List.mem_append_right _ he

/-- Every recorded call certificate has its structural κ-gadget present. -/
def BState.CallCertificatesValid (s : BState) : Prop := s.CallGadgetsValid

def Builder.PreservesCallCertificates (m : Builder α) : Prop :=
  ∀ b, b.CallCertificatesValid → (StateT.run m b).2.CallCertificatesValid

theorem Builder.preserves_bind {α β} (m : Builder α) (k : α → Builder β)
    (hm : m.PreservesCallCertificates)
    (hk : ∀ a, (k a).PreservesCallCertificates) :
    (m >>= k).PreservesCallCertificates := by
  intro b hb
  simp only [StateT.run_bind]
  generalize hrun : StateT.run m b = out
  rcases out with ⟨a, b'⟩
  have hmb := hm b hb
  rw [hrun] at hmb
  simpa using hk a b' hmb

theorem Builder.addNode_preserves_callCertificates (k : NodeKind) :
    (Builder.addNode k).PreservesCallCertificates := by
  intro b hvalid
  exact Builder.addNode_preserves_callGadgetsValid b k hvalid

theorem Builder.addEdge_preserves_callCertificates (src dst : NodeID) :
    (Builder.addEdge src dst).PreservesCallCertificates := by
  intro b hvalid
  exact Builder.addEdge_preserves_callGadgetsValid b src dst hvalid

theorem Builder.addCallNodeWithLam_preserves_callCertificates (f : String) :
    (Builder.addCallNodeWithLam f).PreservesCallCertificates := by
  intro b hvalid
  exact Builder.addCallNodeWithLam_preserves_callGadgetsValid b f hvalid

theorem Builder.addCallGadget_preserves_callCertificates (site : CallGadget) :
    (Builder.addCallGadget site).PreservesCallCertificates := by
  intro b hvalid
  exact Builder.addCallGadget_preserves_callGadgetsValid b site hvalid

theorem lowerStmt_preserves_callCertificates (Φ : FunEnv) (s : Stmt) :
    (lowerStmt Φ s).PreservesCallCertificates := by
  induction s with
  | Skip => simpa [lowerStmt] using Builder.addNode_preserves_callCertificates NodeKind.Skip
  | Decl x e | Assign x e =>
    simpa [lowerStmt] using Builder.addNode_preserves_callCertificates (NodeKind.Assign x e)
  | Invoke => simpa [lowerStmt] using Builder.addNode_preserves_callCertificates NodeKind.Invoke
  | Seq s₁ s₂ ih₁ ih₂ =>
    simp only [lowerStmt]
    refine Builder.preserves_bind _ _ ih₁ ?_
    intro pair₁
    refine Builder.preserves_bind _ _ ih₂ ?_
    intro pair
    exact Builder.addEdge_preserves_callCertificates pair₁.2 pair.1
  | If c t f iht ihf =>
    simp only [lowerStmt]
    refine Builder.preserves_bind _ _ (Builder.addNode_preserves_callCertificates NodeKind.Skip) ?_
    intro en
    refine Builder.preserves_bind _ _ (Builder.addNode_preserves_callCertificates (.Assume c)) ?_
    intro atru
    refine Builder.preserves_bind _ _ (Builder.addNode_preserves_callCertificates (.Assume c.Not)) ?_
    intro afls
    refine Builder.preserves_bind _ _ iht ?_
    intro pairT
    refine Builder.preserves_bind _ _ ihf ?_
    intro pairF
    refine Builder.preserves_bind _ _ (Builder.addNode_preserves_callCertificates NodeKind.Skip) ?_
    intro ex
    refine Builder.preserves_bind _ _ (Builder.addEdge_preserves_callCertificates en atru) ?_
    intro _
    refine Builder.preserves_bind _ _ (Builder.addEdge_preserves_callCertificates en afls) ?_
    intro _
    refine Builder.preserves_bind _ _ (Builder.addEdge_preserves_callCertificates atru pairT.1) ?_
    intro _
    refine Builder.preserves_bind _ _ (Builder.addEdge_preserves_callCertificates afls pairF.1) ?_
    intro _
    refine Builder.preserves_bind _ _ (Builder.addEdge_preserves_callCertificates pairT.2 ex) ?_
    intro _
    exact Builder.addEdge_preserves_callCertificates pairF.2 ex
  | While c body ih =>
    simp only [lowerStmt]
    refine Builder.preserves_bind _ _ (Builder.addNode_preserves_callCertificates NodeKind.Skip) ?_
    intro en
    refine Builder.preserves_bind _ _ (Builder.addNode_preserves_callCertificates (.Assume c)) ?_
    intro atru
    refine Builder.preserves_bind _ _ (Builder.addNode_preserves_callCertificates (.Assume c.Not)) ?_
    intro afls
    refine Builder.preserves_bind _ _ ih ?_
    intro pair
    refine Builder.preserves_bind _ _ (Builder.addEdge_preserves_callCertificates en atru) ?_
    intro _
    refine Builder.preserves_bind _ _ (Builder.addEdge_preserves_callCertificates en afls) ?_
    intro _
    refine Builder.preserves_bind _ _ (Builder.addEdge_preserves_callCertificates atru pair.1) ?_
    intro _
    exact Builder.addEdge_preserves_callCertificates pair.2 en
  | Call f body ih =>
    simp only [lowerStmt]
    refine Builder.preserves_bind _ _ (Builder.addCallNodeWithLam_preserves_callCertificates f) ?_
    intro pair
    refine Builder.preserves_bind _ _ ih ?_
    intro bodyPair
    refine Builder.preserves_bind _ _ (Builder.addNode_preserves_callCertificates NodeKind.Skip) ?_
    intro ret
    exact Builder.addCallGadget_preserves_callCertificates
      ⟨pair.1, f, pair.2, callKind Φ f, bodyPair.1, bodyPair.2, ret, body⟩

/-- Lowering a call emits the complete κ-gadget for its fresh call node. -/
theorem lowerStmt_call_gadget (Φ : FunEnv) (f : String) (lam : Stmt) (b : BState) :
    let (res, b') := (lowerStmt Φ (.Call f lam)).run b
    ∃ enL exL r, res = (b.nextID, r) ∧
      b'.cfg.HasKappaGadget (callKind Φ f) b.nextID enL exL r := by
  simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addCallNodeWithLam_run,
    addNode_run, addCallGadget_run]
  rcases hrun : StateT.run (lowerStmt Φ lam)
      { cfg := { b.cfg with nodes := b.cfg.nodes ++ [.Call f b.nextLam] },
        nextID := b.nextID + 1, nextLam := b.nextLam + 1,
        callGadgets := b.callGadgets } with ⟨⟨enL, exL⟩, bl⟩
  refine ⟨enL, exL, bl.nextID, rfl, ?_⟩
  intro e he
  exact List.mem_append_right _ he

/-- The concrete fragment appended by one lowering run.  Naming the fragment
keeps clients independent of the builder's nested existential witnesses. -/
structure LoweredFragment where
  entry : NodeID
  exit : NodeID
  nodesAdded : List NodeKind
  edgesAdded : List Edge
  gadgetsAdded : List CallGadget

/-- The append-relative semantic contract of `lowerStmt`.  All raw `StateM`
and list bookkeeping is confined to the proof that constructs this record. -/
structure LoweringInvariant (before after : BState) (fragment : LoweredFragment) : Prop where
  stateConsistent : after.nextID = after.cfg.nodes.length
  nodesAppend : after.cfg.nodes = before.cfg.nodes ++ fragment.nodesAdded
  edgesAppend : after.cfg.edges = before.cfg.edges ++ fragment.edgesAdded
  gadgetsAppend : after.callGadgets = before.callGadgets ++ fragment.gadgetsAdded
  edgesBounded : ∀ e ∈ fragment.edgesAdded,
    e.src < after.cfg.nodes.length ∧ e.dst < after.cfg.nodes.length
  progress : ∀ n, before.nextID ≤ n → n < after.nextID → n ≠ fragment.exit →
    ∃ n', (⟨n, n', .plain⟩ : Edge) ∈ fragment.edgesAdded
  endpointsBounded : fragment.entry < after.cfg.nodes.length ∧
    fragment.exit < after.cfg.nodes.length

private theorem lowerStmt_raw_spec (Φ : FunEnv) (s : Stmt) (b : BState)
    (hinv : b.nextID = b.cfg.nodes.length) :
    let (res, b') := (lowerStmt Φ s).run b
    b'.nextID = b'.cfg.nodes.length ∧
    (∃ ns, b'.cfg.nodes = b.cfg.nodes ++ ns) ∧
    (∃ es, b'.cfg.edges = b.cfg.edges ++ es ∧
      (∀ e ∈ es, e.src < b'.cfg.nodes.length ∧
        e.dst < b'.cfg.nodes.length) ∧
      (∀ n, b.nextID ≤ n → n < b'.nextID → n ≠ res.2 →
        ∃ n', (⟨n, n', .plain⟩ : Edge) ∈ es)) ∧
    res.1 < b'.cfg.nodes.length ∧
    res.2 < b'.cfg.nodes.length := by
  induction s generalizing b with
  | Skip => simp [lowerStmt, Builder.addNode, hinv]; grind -- one fresh node
  | Decl x e | Assign x e => simp [lowerStmt, Builder.addNode, hinv]; grind
  | Invoke => simp [lowerStmt, Builder.addNode, hinv]; grind -- one fresh node
  | Call f body ih =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addCallNodeWithLam_run,
      addNode_run, addCallGadget_run]
    -- lower the body `{ s }` in the state after adding the `call f` node
    have hb0 : (b.nextID + 1) = (b.cfg.nodes ++ [NodeKind.Call f b.nextLam]).length := by
      simp; grind
    have hbody := ih
      { cfg := { nodes := b.cfg.nodes ++ [NodeKind.Call f b.nextLam],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1, nextLam := b.nextLam + 1,
        callGadgets := b.callGadgets } hb0
    rcases hrb : StateT.run (lowerStmt Φ body)
      { cfg := { nodes := b.cfg.nodes ++ [NodeKind.Call f b.nextLam],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1, nextLam := b.nextLam + 1,
        callGadgets := b.callGadgets } with ⟨⟨enL, exL⟩, bb⟩
    rw [hrb] at hbody
    simp only at hbody
    obtain ⟨hinvb, ⟨nsb, hnsb⟩, ⟨esb, hesb, hbb, hedb⟩, henL, hexL⟩ := hbody
    -- abbreviations: `en = b.nextID` is the call node, `r = bb.nextID` the return node
    have hmono : b.nextID + 1 ≤ bb.nextID := by rw [hinvb, hnsb]; simp; grind
    have hlen : bb.nextID = bb.cfg.nodes.length := hinvb
    refine ⟨by simp [hinvb], ?_, ?_, by simp; grind, by simp; grind⟩
    · exact ⟨[NodeKind.Call f b.nextLam] ++ nsb ++ [NodeKind.Skip],
        by rw [hnsb]; simp [List.append_assoc]⟩
    · refine ⟨esb ++ kappaEdges (callKind Φ f) b.nextID enL exL bb.nextID,
        by rw [hesb]; simp [CallGadget.edges, List.append_assoc], ?_⟩
      constructor
      · intro e he
        simp only [List.mem_append] at he
        rcases he with he | he
        · have := hbb e he; simp; grind
        · have := kappaEdges_mem _ _ _ _ _ _ he
          simp; grind
      · intro n hn1 hn2 hn3
        dsimp only at hn2 hn3
        by_cases h0 : n = b.nextID
        · exact ⟨enL, by
            apply List.mem_append_right
            subst h0; exact kappaEdges_en_enL _ _ _ _ _⟩
        · have hn1' : b.nextID + 1 ≤ n := by grind
          by_cases hexeq : n = exL
          · exact ⟨bb.nextID, by
              apply List.mem_append_right
              subst hexeq; exact kappaEdges_exL_r _ _ _ _ _⟩
          · obtain ⟨n', hn'⟩ := hedb n hn1' (by grind) hexeq
            exact ⟨n', List.mem_append_left _ hn'⟩
  | Seq s₁ s₂ ih₁ ih₂ =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure]
    rcases hr₁ : StateT.run (lowerStmt Φ s₁) b with ⟨⟨en₁, ex₁⟩, b₁⟩
    have h₁ := ih₁ b hinv
    rw [hr₁] at h₁
    simp only at h₁
    obtain ⟨hinv₁, ⟨ns₁, hns₁⟩, ⟨es₁, hes₁, hb₁, hedge₁⟩, hen₁, hex₁⟩ := h₁
    rcases hr₂ : StateT.run (lowerStmt Φ s₂) b₁ with ⟨⟨en₂, ex₂⟩, b₂⟩
    have h₂ := ih₂ b₁ hinv₁
    rw [hr₂] at h₂
    simp only at h₂
    obtain ⟨hinv₂, ⟨ns₂, hns₂⟩, ⟨es₂, hes₂, hb₂, hedge₂⟩, hen₂, hex₂⟩ := h₂
    simp only [addEdge_run]
    have hmono : b₁.cfg.nodes.length ≤ b₂.cfg.nodes.length := by rw [hns₂]; simp
    refine ⟨by simpa using hinv₂, ⟨ns₁ ++ ns₂, by rw [hns₂, hns₁]; simp⟩,
      ⟨es₁ ++ es₂ ++ [⟨ex₁, en₂, .plain⟩], by simp [hes₂, hes₁, List.append_assoc], ?_⟩,
      by grind, by simpa using hex₂⟩
    constructor
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
        nextID := b.nextID + 1 + 1 + 1, nextLam := b.nextLam,
        callGadgets := b.callGadgets } hbt0
    rcases hrt : StateT.run (lowerStmt Φ t)
      { cfg := { nodes := b.cfg.nodes ++ [NodeKind.Skip] ++ [NodeKind.Assume c] ++
                  [NodeKind.Assume c.Not],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1 + 1 + 1, nextLam := b.nextLam,
        callGadgets := b.callGadgets } with ⟨⟨ent, ext⟩, bt⟩
    rw [hrt] at ht
    simp only at ht
    obtain ⟨hinvt, ⟨nst, hnst⟩, ⟨est, hest, hbt, hedt⟩, hent, hext⟩ := ht
    have hf := ih_f bt hinvt
    rcases hrf : StateT.run (lowerStmt Φ f) bt with ⟨⟨enf, exf⟩, bf⟩
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
    · refine ⟨est ++ esf ++ [⟨b.nextID, b.nextID + 1, .plain⟩, ⟨b.nextID, b.nextID + 1 + 1, .plain⟩,
        ⟨b.nextID + 1, ent, .plain⟩, ⟨b.nextID + 1 + 1, enf, .plain⟩,
        ⟨ext, bf.nextID, .plain⟩, ⟨exf, bf.nextID, .plain⟩],
        by rw [hesf, hest]; simp [List.append_assoc], ?_⟩
      constructor
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
        nextID := b.nextID + 1 + 1 + 1, nextLam := b.nextLam,
        callGadgets := b.callGadgets } hbb0
    rcases hrb : StateT.run (lowerStmt Φ body)
      { cfg := { nodes := b.cfg.nodes ++ [NodeKind.Skip] ++ [NodeKind.Assume c] ++
                    [NodeKind.Assume c.Not],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1 + 1 + 1, nextLam := b.nextLam,
        callGadgets := b.callGadgets } with ⟨⟨enb, exb⟩, bb⟩
    rw [hrb] at hb
    simp only at hb
    obtain ⟨hinvb, ⟨nsb, hnsb⟩, ⟨esb, hesb, hbb, hedb⟩, henb, hexb⟩ := hb
    have hL1 : b.cfg.nodes.length + 3 ≤ bb.cfg.nodes.length := by
      rw [hnsb]; grind
    refine ⟨by simp [hinvb], ?_, ?_, by simp; grind, by simp; grind⟩
    · exact ⟨[NodeKind.Skip, NodeKind.Assume c, NodeKind.Assume c.Not] ++ nsb,
        by rw [hnsb]; simp [List.append_assoc]⟩
    · refine ⟨esb ++ [⟨b.nextID, b.nextID + 1, .plain⟩, ⟨b.nextID, b.nextID + 1 + 1, .plain⟩,
        ⟨b.nextID + 1, enb, .plain⟩, ⟨exb, b.nextID, .plain⟩],
        by rw [hesb]; simp [List.append_assoc], ?_⟩
      constructor
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

/-- A builder computation preserves its input gadget list as a prefix. -/
def Builder.AppendsCallGadgets (m : Builder α) : Prop :=
  ∀ b, ∃ gs, (StateT.run m b).2.callGadgets = b.callGadgets ++ gs

theorem Builder.appendsCallGadgets_bind {α β} (m : Builder α) (k : α → Builder β)
    (hm : m.AppendsCallGadgets) (hk : ∀ a, (k a).AppendsCallGadgets) :
    (m >>= k).AppendsCallGadgets := by
  intro b
  rcases hrunM : StateT.run m b with ⟨a, b'⟩
  have h₁ := hm b
  rw [hrunM] at h₁
  simp only at h₁
  obtain ⟨gs₁, hgs₁⟩ := h₁
  rcases hrunK : StateT.run (k a) b' with ⟨result, b''⟩
  have h₂ := hk a b'
  rw [hrunK] at h₂
  simp only at h₂
  obtain ⟨gs₂, hgs₂⟩ := h₂
  refine ⟨gs₁ ++ gs₂, ?_⟩
  simp only [StateT.run_bind]
  rw [hrunM]
  change (StateT.run (k a) b').2.callGadgets = b.callGadgets ++ (gs₁ ++ gs₂)
  rw [hrunK]
  exact hgs₂.trans (by rw [hgs₁, List.append_assoc])

theorem Builder.addNode_appendsCallGadgets (k : NodeKind) :
    (Builder.addNode k).AppendsCallGadgets := by
  intro b
  exact ⟨[], by simp⟩

theorem Builder.addEdge_appendsCallGadgets (src dst : NodeID) :
    (Builder.addEdge src dst).AppendsCallGadgets := by
  intro b
  exact ⟨[], by simp⟩

theorem Builder.addCallNodeWithLam_appendsCallGadgets (f : String) :
    (Builder.addCallNodeWithLam f).AppendsCallGadgets := by
  intro b
  exact ⟨[], by simp⟩

theorem Builder.addCallGadget_appendsCallGadgets (site : CallGadget) :
    (Builder.addCallGadget site).AppendsCallGadgets := by
  intro b
  exact ⟨[site], by simp⟩

theorem lowerStmt_appendsCallGadgets (Φ : FunEnv) (s : Stmt) :
    (lowerStmt Φ s).AppendsCallGadgets := by
  induction s with
  | Skip => simpa [lowerStmt] using Builder.addNode_appendsCallGadgets NodeKind.Skip
  | Decl x e | Assign x e =>
    simpa [lowerStmt] using Builder.addNode_appendsCallGadgets (NodeKind.Assign x e)
  | Invoke => simpa [lowerStmt] using Builder.addNode_appendsCallGadgets NodeKind.Invoke
  | Seq s₁ s₂ ih₁ ih₂ =>
    simp only [lowerStmt]
    refine Builder.appendsCallGadgets_bind _ _ ih₁ ?_
    intro pair₁
    refine Builder.appendsCallGadgets_bind _ _ ih₂ ?_
    intro pair₂
    exact Builder.addEdge_appendsCallGadgets pair₁.2 pair₂.1
  | If c t f iht ihf =>
    simp only [lowerStmt]
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addNode_appendsCallGadgets NodeKind.Skip) ?_
    intro en
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addNode_appendsCallGadgets (.Assume c)) ?_
    intro atru
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addNode_appendsCallGadgets (.Assume c.Not)) ?_
    intro afls
    refine Builder.appendsCallGadgets_bind _ _ iht ?_
    intro pairT
    refine Builder.appendsCallGadgets_bind _ _ ihf ?_
    intro pairF
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addNode_appendsCallGadgets NodeKind.Skip) ?_
    intro ex
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addEdge_appendsCallGadgets en atru) ?_
    intro _
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addEdge_appendsCallGadgets en afls) ?_
    intro _
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addEdge_appendsCallGadgets atru pairT.1) ?_
    intro _
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addEdge_appendsCallGadgets afls pairF.1) ?_
    intro _
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addEdge_appendsCallGadgets pairT.2 ex) ?_
    intro _
    exact Builder.addEdge_appendsCallGadgets pairF.2 ex
  | While c body ih =>
    simp only [lowerStmt]
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addNode_appendsCallGadgets NodeKind.Skip) ?_
    intro en
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addNode_appendsCallGadgets (.Assume c)) ?_
    intro atru
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addNode_appendsCallGadgets (.Assume c.Not)) ?_
    intro afls
    refine Builder.appendsCallGadgets_bind _ _ ih ?_
    intro pair
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addEdge_appendsCallGadgets en atru) ?_
    intro _
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addEdge_appendsCallGadgets en afls) ?_
    intro _
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addEdge_appendsCallGadgets atru pair.1) ?_
    intro _
    exact Builder.addEdge_appendsCallGadgets pair.2 en
  | Call f body ih =>
    simp only [lowerStmt]
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addCallNodeWithLam_appendsCallGadgets f) ?_
    intro pair
    refine Builder.appendsCallGadgets_bind _ _ ih ?_
    intro bodyPair
    refine Builder.appendsCallGadgets_bind _ _
      (Builder.addNode_appendsCallGadgets NodeKind.Skip) ?_
    intro ret
    exact Builder.addCallGadget_appendsCallGadgets
      ⟨pair.1, f, pair.2, callKind Φ f, bodyPair.1, bodyPair.2, ret, body⟩

/-- Lowering only appends call-gadget provenance. -/
theorem lowerStmt_callGadgets_append (Φ : FunEnv) (s : Stmt) (b : BState) :
    let (_, b') := (lowerStmt Φ s).run b
    ∃ gs, b'.callGadgets = b.callGadgets ++ gs :=
  lowerStmt_appendsCallGadgets Φ s b

/-- Certified lowering packages the complete fresh fragment behind named
projections.  This is the primary correctness API for builder clients. -/
theorem lowerStmt_certified (Φ : FunEnv) (s : Stmt) (b : BState)
    (hinv : b.nextID = b.cfg.nodes.length) :
    let (res, b') := (lowerStmt Φ s).run b
    ∃ fragment : LoweredFragment,
      res = (fragment.entry, fragment.exit) ∧
      LoweringInvariant b b' fragment := by
  rcases hrun : (lowerStmt Φ s).run b with ⟨⟨entry, exit⟩, b'⟩
  have hraw := lowerStmt_raw_spec Φ s b hinv
  have hgadgets := lowerStmt_callGadgets_append Φ s b
  rw [hrun] at hraw hgadgets
  simp only at hraw hgadgets ⊢
  obtain ⟨hstate, ⟨nodes, hnodes⟩,
    ⟨edges, hedges, hbounds, hprogress⟩, hentry, hexit⟩ := hraw
  obtain ⟨gadgets, hgadgets⟩ := hgadgets
  refine ⟨⟨entry, exit, nodes, edges, gadgets⟩, rfl, ?_⟩
  exact {
    stateConsistent := hstate
    nodesAppend := hnodes
    edgesAppend := hedges
    gadgetsAppend := hgadgets
    edgesBounded := hbounds
    progress := hprogress
    endpointsBounded := ⟨hentry, hexit⟩ }

/-- Compatibility view of `lowerStmt_certified`.  Existing clients keep the
original statement while new proofs consume named invariant projections. -/
theorem lowerStmt_spec (Φ : FunEnv) (s : Stmt) (b : BState)
    (hinv : b.nextID = b.cfg.nodes.length) :
    let (res, b') := (lowerStmt Φ s).run b
    b'.nextID = b'.cfg.nodes.length ∧
    (∃ ns, b'.cfg.nodes = b.cfg.nodes ++ ns) ∧
    (∃ es, b'.cfg.edges = b.cfg.edges ++ es ∧
      (∀ e ∈ es, e.src < b'.cfg.nodes.length ∧
        e.dst < b'.cfg.nodes.length) ∧
      (∀ n, b.nextID ≤ n → n < b'.nextID → n ≠ res.2 →
        ∃ n', (⟨n, n', .plain⟩ : Edge) ∈ es)) ∧
    res.1 < b'.cfg.nodes.length ∧
    res.2 < b'.cfg.nodes.length := by
  rcases hrun : (lowerStmt Φ s).run b with ⟨⟨entry, exit⟩, b'⟩
  have hcert := lowerStmt_certified Φ s b hinv
  rw [hrun] at hcert
  simp only at hcert ⊢
  obtain ⟨fragment, hres, hfragment⟩ := hcert
  cases hres
  exact ⟨hfragment.stateConsistent,
    ⟨fragment.nodesAdded, hfragment.nodesAppend⟩,
    ⟨fragment.edgesAdded, hfragment.edgesAppend, hfragment.edgesBounded,
      hfragment.progress⟩,
    hfragment.endpointsBounded.1, hfragment.endpointsBounded.2⟩

/-- The κ-gadget of a directly lowered call belongs to the newly appended edge
fragment, rather than merely to the final graph (which may have an arbitrary
prefix). -/
theorem lowerStmt_call_gadget_fragment (Φ : FunEnv) (f : String) (lam : Stmt) (b : BState)
    (hinv : b.nextID = b.cfg.nodes.length) :
    let (res, b') := (lowerStmt Φ (.Call f lam)).run b
    ∃ enL exL r es, res = (b.nextID, r) ∧ b'.cfg.edges = b.cfg.edges ++ es ∧
      (∀ ⦃e⦄, e ∈ kappaEdges (callKind Φ f) b.nextID enL exL r → e ∈ es) := by
  simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addCallNodeWithLam_run,
    addNode_run, addCallGadget_run]
  rcases hrun : StateT.run (lowerStmt Φ lam)
      { cfg := { b.cfg with nodes := b.cfg.nodes ++ [.Call f b.nextLam] },
        nextID := b.nextID + 1, nextLam := b.nextLam + 1,
        callGadgets := b.callGadgets } with ⟨⟨enL, exL⟩, bl⟩
  have hspec := lowerStmt_spec Φ lam
    { cfg := { b.cfg with nodes := b.cfg.nodes ++ [.Call f b.nextLam] },
      nextID := b.nextID + 1, nextLam := b.nextLam + 1,
      callGadgets := b.callGadgets }
    (by simp; grind)
  rw [hrun] at hspec
  obtain ⟨-, -, ⟨es, hes, -, -⟩, -, -⟩ := hspec
  refine ⟨enL, exL, bl.nextID,
    es ++ kappaEdges (callKind Φ f) b.nextID enL exL bl.nextID, rfl, ?_, ?_⟩
  · rw [hes]
    simp [CallGadget.edges, List.append_assoc]
  · intro e he
    exact List.mem_append_right _ he

/-- The append-relative call-site fact, stated for an arbitrary statement and
    proved by structural induction. Keeping the initial graph explicit is
    important: callers may lower into a nonempty builder while reasoning only
    about the fragment they append. -/
theorem lowerStmt_root_call_gadget (Φ : FunEnv) (s : Stmt) (b : BState)
    (hinv : b.nextID = b.cfg.nodes.length) {f : String} {lam : Stmt}
    (hroot : s = .Call f lam) :
    let (res, b') := (lowerStmt Φ s).run b
    ∃ enL exL r es, res = (b.nextID, r) ∧ b'.cfg.edges = b.cfg.edges ++ es ∧
      b'.cfg.HasKappaGadget (callKind Φ f) b.nextID enL exL r := by
  induction s generalizing b with
  | Skip | Decl | Assign | Seq | If | While | Invoke => cases hroot
  | Call g body ih =>
    cases hroot
    obtain ⟨enL, exL, r, es, hres, hedges, hgadget⟩ :=
      lowerStmt_call_gadget_fragment Φ f lam b hinv
    refine ⟨enL, exL, r, es, hres, hedges, ?_⟩
    intro e he
    rw [hedges]
    exact List.mem_append_right _ (hgadget he)


-- # Builder equivariance: `lowerStmt` output shifts uniformly with the offsets

/-- Shift both endpoints of an edge by `δ`. -/
def Edge.shift (δ : NodeID) (e : Edge) : Edge := ⟨e.src + δ, e.dst + δ, e.kind⟩

/-- Shift the lambda id of a `Call` node by `δL`. -/
def NodeKind.shiftLam (δL : Nat) : NodeKind → NodeKind
  | .Call f ℓ => .Call f (ℓ + δL)
  | k => k

def CFG.HasInlineBodyFragment (Φ : FunEnv) (g : CFG) (site : CallGadget) : Prop :=
  (∀ e ∈ (site.body.generatedCFGFrom Φ (site.lamID + 1)).cfg.edges,
    e.shift site.enL ∈ g.edges) ∧
  (∀ n k, (site.body.generatedCFGFrom Φ (site.lamID + 1)).cfg.nodeKind n = some k →
    g.nodeKind (n + site.enL) = some k)

/-- Inline-body evidence is stable when subsequent lowering appends graph
material.  This is the inherited-site case of the certificate invariant. -/
theorem CFG.HasInlineBodyFragment.mono {Φ : FunEnv} {g g' : CFG}
    {site : CallGadget} {ns : List NodeKind} {es : List Edge}
    (hfragment : g.HasInlineBodyFragment Φ site)
    (hnodes : g'.nodes = g.nodes ++ ns)
    (hedges : g'.edges = g.edges ++ es) :
    g'.HasInlineBodyFragment Φ site := by
  constructor
  · intro e he
    rw [hedges]
    exact List.mem_append_left _ (hfragment.1 e he)
  · intro n k hk
    have hnk := hfragment.2 n k hk
    simp only [CFG.nodeKind] at hnk ⊢
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hnk
    rw [hnodes, List.getElem?_append_left hi]
    exact hnk

/-- Environment-aware provenance for the inline fragments of all call sites
    recorded in a builder state.  This parallel invariant is introduced after
    the fragment contract so its preservation can be proved independently of
    the earlier κ-gadget certificate interface. -/
def BState.InlineFragmentsValid (Φ : FunEnv) (b : BState) : Prop :=
  ∀ site ∈ b.callGadgets, b.cfg.HasInlineBodyFragment Φ site

def Builder.PreservesInlineFragments (Φ : FunEnv) (m : Builder α) : Prop :=
  ∀ b, b.InlineFragmentsValid Φ →
    (StateT.run m b).2.InlineFragmentsValid Φ

theorem Builder.preserves_inlineFragments_bind {α β} (Φ : FunEnv)
    (m : Builder α) (k : α → Builder β)
    (hm : m.PreservesInlineFragments Φ)
    (hk : ∀ a, (k a).PreservesInlineFragments Φ) :
    (m >>= k).PreservesInlineFragments Φ := by
  intro b hb
  simp only [StateT.run_bind]
  generalize hrun : StateT.run m b = out
  rcases out with ⟨a, b'⟩
  have hmb := hm b hb
  rw [hrun] at hmb
  simpa using hk a b' hmb

theorem Builder.addNode_preserves_inlineFragments {Φ : FunEnv}
    (b : BState) (k : NodeKind) (hvalid : b.InlineFragmentsValid Φ) :
    (StateT.run (Builder.addNode k) b).2.InlineFragmentsValid Φ := by
  intro site hsite
  simpa only [addNode_run] using
    CFG.HasInlineBodyFragment.mono (hvalid site (by simpa using hsite))
      (ns := [k]) (es := []) rfl (by simp)

theorem Builder.addEdge_preserves_inlineFragments {Φ : FunEnv}
    (b : BState) (src dst : NodeID) (hvalid : b.InlineFragmentsValid Φ) :
    (StateT.run (Builder.addEdge src dst) b).2.InlineFragmentsValid Φ := by
  intro site hsite
  simpa only [addEdge_run] using
    CFG.HasInlineBodyFragment.mono (hvalid site (by simpa using hsite))
      (ns := []) (es := [⟨src, dst, .plain⟩]) (by simp) rfl

theorem Builder.addCallNodeWithLam_preserves_inlineFragments {Φ : FunEnv}
    (b : BState) (f : String) (hvalid : b.InlineFragmentsValid Φ) :
    (StateT.run (Builder.addCallNodeWithLam f) b).2.InlineFragmentsValid Φ := by
  intro site hsite
  simpa only [addCallNodeWithLam_run] using
    CFG.HasInlineBodyFragment.mono (hvalid site (by simpa using hsite))
      (ns := [.Call f b.nextLam]) (es := []) rfl (by simp)

theorem Builder.addCallGadget_preserves_inlineFragments {Φ : FunEnv}
    (b : BState) (site : CallGadget) (hvalid : b.InlineFragmentsValid Φ)
    (hsite : b.cfg.HasInlineBodyFragment Φ site) :
    (StateT.run (Builder.addCallGadget site) b).2.InlineFragmentsValid Φ := by
  intro other hother
  simp only [addCallGadget_run, List.mem_append, List.mem_singleton] at hother ⊢
  rcases hother with hother | rfl
  · exact CFG.HasInlineBodyFragment.mono (hvalid other hother)
      (ns := []) (es := site.edges) (by simp) rfl
  · exact CFG.HasInlineBodyFragment.mono hsite
      (ns := []) (es := other.edges) (by simp) rfl

theorem Builder.addNode_preservesInlineFragments (Φ : FunEnv) (k : NodeKind) :
    (Builder.addNode k).PreservesInlineFragments Φ := by
  intro b hb
  exact Builder.addNode_preserves_inlineFragments b k hb

theorem Builder.addEdge_preservesInlineFragments (Φ : FunEnv) (src dst : NodeID) :
    (Builder.addEdge src dst).PreservesInlineFragments Φ := by
  intro b hb
  exact Builder.addEdge_preserves_inlineFragments b src dst hb

theorem Builder.addCallNodeWithLam_preservesInlineFragments (Φ : FunEnv) (f : String) :
    (Builder.addCallNodeWithLam f).PreservesInlineFragments Φ := by
  intro b hb
  exact Builder.addCallNodeWithLam_preserves_inlineFragments b f hb

/-- The κ-gadget of a call site is equivariant under a uniform node-id shift:
    shifting the four site nodes by `δ` shifts every emitted edge by `δ`. -/
theorem kappaEdges_shift (κ : InvKind) (en enL exL r δ : NodeID) :
    kappaEdges κ (en+δ) (enL+δ) (exL+δ) (r+δ) =
      (kappaEdges κ en enL exL r).map (Edge.shift δ) := by
  cases κ <;> simp [kappaEdges, Edge.shift]

-- The proof is a *doubled* state-monad induction over `Stmt` (it runs `lowerStmt`
-- from two states at once and matches the fragments).
/-- **Builder equivariance for `lowerStmt`.** Running
    `lowerStmt Φ s` from two builder states that differ only by a `nextID`
    offset `δ` and a `nextLam` offset `δL` produces the *same* CFG fragment up
    to those two shifts. -/
theorem lowerStmt_equivariant (Φ : FunEnv) (s : Stmt) :
    ∀ (b₁ b₂ : BState) (δ δL : Nat),
    b₂.nextID = b₁.nextID + δ → b₂.nextLam = b₁.nextLam + δL →
    let (r₁, b₁') := (lowerStmt Φ s).run b₁
    let (r₂, b₂') := (lowerStmt Φ s).run b₂
    r₂.1 = r₁.1 + δ ∧ r₂.2 = r₁.2 + δ ∧
    b₂'.nextID = b₁'.nextID + δ ∧
    b₂'.nextLam = b₁'.nextLam + δL ∧
    (∃ ns₁ ns₂, b₁'.cfg.nodes = b₁.cfg.nodes ++ ns₁ ∧
                b₂'.cfg.nodes = b₂.cfg.nodes ++ ns₂ ∧
                ns₂ = ns₁.map (NodeKind.shiftLam δL)) ∧
    (∃ es₁ es₂, b₁'.cfg.edges = b₁.cfg.edges ++ es₁ ∧
                b₂'.cfg.edges = b₂.cfg.edges ++ es₂ ∧
                es₂ = es₁.map (Edge.shift δ)) := by
  induction s with
  | Skip =>
    intro b₁ b₂ δ δL hid hlam
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run]
    refine ⟨hid, hid, by grind, hlam,
      ⟨[.Skip], [.Skip], rfl, rfl, rfl⟩,
      ⟨[], [], (List.append_nil _).symm, (List.append_nil _).symm, rfl⟩⟩
  | Decl x e | Assign x e =>
    intro b₁ b₂ δ δL hid hlam
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run]
    refine ⟨hid, hid, by grind, hlam,
      ⟨[.Assign x e], [.Assign x e], rfl, rfl, rfl⟩,
      ⟨[], [], (List.append_nil _).symm, (List.append_nil _).symm, rfl⟩⟩
  | Invoke =>
    intro b₁ b₂ δ δL hid hlam
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run]
    refine ⟨hid, hid, by grind, hlam,
      ⟨[.Invoke], [.Invoke], rfl, rfl, rfl⟩,
      ⟨[], [], (List.append_nil _).symm, (List.append_nil _).symm, rfl⟩⟩
  | Seq s₁ s₂ ih₁ ih₂ =>
    intro b₁ b₂ δ δL hid hlam
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure]
    rcases hr₁ : StateT.run (lowerStmt Φ s₁) b₁ with ⟨⟨en₁, ex₁⟩, a₁⟩
    rcases hr₁' : StateT.run (lowerStmt Φ s₁) b₂ with ⟨⟨en₁', ex₁'⟩, a₂⟩
    have H₁ := ih₁ b₁ b₂ δ δL hid hlam
    rw [hr₁, hr₁'] at H₁; simp only at H₁
    obtain ⟨he1, hx1, hidA, hlamA, ⟨n1, n1', hn1, hn1', hn1m⟩,
      ⟨e1, e1', he1e, he1e', he1m⟩⟩ := H₁
    rcases hs₁ : StateT.run (lowerStmt Φ s₂) a₁ with ⟨⟨en₂, ex₂⟩, c₁⟩
    rcases hs₁' : StateT.run (lowerStmt Φ s₂) a₂ with ⟨⟨en₂', ex₂'⟩, c₂⟩
    have H₂ := ih₂ a₁ a₂ δ δL hidA hlamA
    rw [hs₁, hs₁'] at H₂; simp only at H₂
    obtain ⟨he2, hx2, hidB, hlamB, ⟨n2, n2', hn2, hn2', hn2m⟩,
      ⟨f2, f2', hf2e, hf2e', hf2m⟩⟩ := H₂
    simp only [addEdge_run]
    refine ⟨he1, hx2, hidB, hlamB,
      ⟨n1 ++ n2, n1' ++ n2', ?_, ?_, ?_⟩,
      ⟨e1 ++ f2 ++ [⟨ex₁, en₂, .plain⟩], e1' ++ f2' ++ [⟨ex₁', en₂', .plain⟩], ?_, ?_, ?_⟩⟩
    · rw [hn2, hn1, List.append_assoc]
    · rw [hn2', hn1', List.append_assoc]
    · rw [hn1m, hn2m, List.map_append]
    · rw [hf2e, he1e]; simp only [List.append_assoc]
    · rw [hf2e', he1e']; simp only [List.append_assoc]
    · rw [hf2m, he1m, List.map_append, List.map_append]
      simp only [List.map_cons, List.map_nil, Edge.shift]
      grind
  | If c t f ih_t ih_f =>
    intro b₁ b₂ δ δL hid hlam
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run, addEdge_run]
    rcases hrt : StateT.run (lowerStmt Φ t)
        { cfg := { nodes := b₁.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                   edges := b₁.cfg.edges, entry := b₁.cfg.entry, exit := b₁.cfg.exit },
          nextID := b₁.nextID + 1 + 1 + 1, nextLam := b₁.nextLam,
          callGadgets := b₁.callGadgets } with ⟨⟨ent, ext⟩, ct₁⟩
    rcases hrt' : StateT.run (lowerStmt Φ t)
        { cfg := { nodes := b₂.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                   edges := b₂.cfg.edges, entry := b₂.cfg.entry, exit := b₂.cfg.exit },
          nextID := b₂.nextID + 1 + 1 + 1, nextLam := b₂.nextLam,
          callGadgets := b₂.callGadgets } with ⟨⟨ent', ext'⟩, ct₂⟩
    have Ht := ih_t
        { cfg := { nodes := b₁.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                   edges := b₁.cfg.edges, entry := b₁.cfg.entry, exit := b₁.cfg.exit },
          nextID := b₁.nextID + 1 + 1 + 1, nextLam := b₁.nextLam,
          callGadgets := b₁.callGadgets }
        { cfg := { nodes := b₂.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                   edges := b₂.cfg.edges, entry := b₂.cfg.entry, exit := b₂.cfg.exit },
          nextID := b₂.nextID + 1 + 1 + 1, nextLam := b₂.nextLam,
          callGadgets := b₂.callGadgets }
        δ δL (by simp; grind) (by simp; grind)
    rw [hrt, hrt'] at Ht; simp only at Ht
    obtain ⟨het, hxt, hidt, hlamt, ⟨nt, nt', hnt, hnt', hntm⟩,
      ⟨et, et', hete, hete', hetm⟩⟩ := Ht
    rcases hrf : StateT.run (lowerStmt Φ f) ct₁ with ⟨⟨enf, exf⟩, cf₁⟩
    rcases hrf' : StateT.run (lowerStmt Φ f) ct₂ with ⟨⟨enf', exf'⟩, cf₂⟩
    have Hf := ih_f ct₁ ct₂ δ δL hidt hlamt
    rw [hrf, hrf'] at Hf; simp only at Hf
    obtain ⟨hef, hxf, hidf, hlamf, ⟨nf, nf', hnf, hnf', hnfm⟩,
      ⟨ef, ef', hefe, hefe', hefm⟩⟩ := Hf
    refine ⟨hid, hidf, by grind, hlamf,
      ⟨[.Skip, .Assume c, .Assume (.Not c)] ++ nt ++ nf ++ [.Skip],
       [.Skip, .Assume c, .Assume (.Not c)] ++ nt' ++ nf' ++ [.Skip], ?_, ?_, ?_⟩,
      ⟨et ++ ef ++ [⟨b₁.nextID, b₁.nextID+1, .plain⟩, ⟨b₁.nextID, b₁.nextID+1+1, .plain⟩,
             ⟨b₁.nextID+1, ent, .plain⟩, ⟨b₁.nextID+1+1, enf, .plain⟩,
             ⟨ext, cf₁.nextID, .plain⟩, ⟨exf, cf₁.nextID, .plain⟩],
       et' ++ ef' ++ [⟨b₂.nextID, b₂.nextID+1, .plain⟩, ⟨b₂.nextID, b₂.nextID+1+1, .plain⟩,
              ⟨b₂.nextID+1, ent', .plain⟩, ⟨b₂.nextID+1+1, enf', .plain⟩,
              ⟨ext', cf₂.nextID, .plain⟩, ⟨exf', cf₂.nextID, .plain⟩], ?_, ?_, ?_⟩⟩
    · rw [hnf, hnt]; simp [List.append_assoc]
    · rw [hnf', hnt']; simp [List.append_assoc]
    · rw [hntm, hnfm]
      simp only [List.map_append, List.map_cons, List.map_nil, NodeKind.shiftLam]
    · rw [hefe, hete]; simp [List.append_assoc]
    · rw [hefe', hete']; simp [List.append_assoc]
    · rw [hetm, hefm]
      simp only [List.map_append, List.map_cons, List.map_nil, Edge.shift]
      grind
  | While c body ih_b =>
    intro b₁ b₂ δ δL hid hlam
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run, addEdge_run]
    rcases hrb : StateT.run (lowerStmt Φ body)
        { cfg := { nodes := b₁.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                   edges := b₁.cfg.edges, entry := b₁.cfg.entry, exit := b₁.cfg.exit },
          nextID := b₁.nextID + 1 + 1 + 1, nextLam := b₁.nextLam,
          callGadgets := b₁.callGadgets } with ⟨⟨enb, exb⟩, cb₁⟩
    rcases hrb' : StateT.run (lowerStmt Φ body)
        { cfg := { nodes := b₂.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                   edges := b₂.cfg.edges, entry := b₂.cfg.entry, exit := b₂.cfg.exit },
          nextID := b₂.nextID + 1 + 1 + 1, nextLam := b₂.nextLam,
          callGadgets := b₂.callGadgets } with ⟨⟨enb', exb'⟩, cb₂⟩
    have Hb := ih_b
        { cfg := { nodes := b₁.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                   edges := b₁.cfg.edges, entry := b₁.cfg.entry, exit := b₁.cfg.exit },
          nextID := b₁.nextID + 1 + 1 + 1, nextLam := b₁.nextLam,
          callGadgets := b₁.callGadgets }
        { cfg := { nodes := b₂.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                   edges := b₂.cfg.edges, entry := b₂.cfg.entry, exit := b₂.cfg.exit },
          nextID := b₂.nextID + 1 + 1 + 1, nextLam := b₂.nextLam,
          callGadgets := b₂.callGadgets }
        δ δL (by simp; grind) (by simp; grind)
    rw [hrb, hrb'] at Hb; simp only at Hb
    obtain ⟨heb, hxb, hidb, hlamb, ⟨nb, nb', hnb, hnb', hnbm⟩,
      ⟨eb, eb', hebe, hebe', hebm⟩⟩ := Hb
    refine ⟨hid, by grind, hidb, hlamb,
      ⟨[.Skip, .Assume c, .Assume (.Not c)] ++ nb,
       [.Skip, .Assume c, .Assume (.Not c)] ++ nb', ?_, ?_, ?_⟩,
      ⟨eb ++ [⟨b₁.nextID, b₁.nextID+1, .plain⟩, ⟨b₁.nextID, b₁.nextID+1+1, .plain⟩,
             ⟨b₁.nextID+1, enb, .plain⟩, ⟨exb, b₁.nextID, .plain⟩],
       eb' ++ [⟨b₂.nextID, b₂.nextID+1, .plain⟩, ⟨b₂.nextID, b₂.nextID+1+1, .plain⟩,
              ⟨b₂.nextID+1, enb', .plain⟩, ⟨exb', b₂.nextID, .plain⟩], ?_, ?_, ?_⟩⟩
    · rw [hnb]; simp [List.append_assoc]
    · rw [hnb']; simp [List.append_assoc]
    · rw [hnbm]; simp [NodeKind.shiftLam]
    · rw [hebe]; simp [List.append_assoc]
    · rw [hebe']; simp [List.append_assoc]
    · rw [hebm]
      simp only [List.map_append, List.map_cons, List.map_nil, Edge.shift]
      grind
  | Call f body ih =>
    intro b₁ b₂ δ δL hid hlam
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addCallNodeWithLam_run,
      addNode_run, addCallGadget_run]
    rcases hrl : StateT.run (lowerStmt Φ body)
        { cfg := { nodes := b₁.cfg.nodes ++ [.Call f b₁.nextLam], edges := b₁.cfg.edges,
                   entry := b₁.cfg.entry, exit := b₁.cfg.exit },
          nextID := b₁.nextID + 1, nextLam := b₁.nextLam + 1,
          callGadgets := b₁.callGadgets } with ⟨⟨enL, exL⟩, cb₁⟩
    rcases hrl' : StateT.run (lowerStmt Φ body)
        { cfg := { nodes := b₂.cfg.nodes ++ [.Call f b₂.nextLam], edges := b₂.cfg.edges,
                   entry := b₂.cfg.entry, exit := b₂.cfg.exit },
          nextID := b₂.nextID + 1, nextLam := b₂.nextLam + 1,
          callGadgets := b₂.callGadgets } with ⟨⟨enL', exL'⟩, cb₂⟩
    have Hl := ih
        { cfg := { nodes := b₁.cfg.nodes ++ [.Call f b₁.nextLam], edges := b₁.cfg.edges,
                   entry := b₁.cfg.entry, exit := b₁.cfg.exit },
          nextID := b₁.nextID + 1, nextLam := b₁.nextLam + 1,
          callGadgets := b₁.callGadgets }
        { cfg := { nodes := b₂.cfg.nodes ++ [.Call f b₂.nextLam], edges := b₂.cfg.edges,
                   entry := b₂.cfg.entry, exit := b₂.cfg.exit },
          nextID := b₂.nextID + 1, nextLam := b₂.nextLam + 1,
          callGadgets := b₂.callGadgets }
        δ δL (by simp; grind) (by simp; grind)
    rw [hrl, hrl'] at Hl; simp only at Hl
    obtain ⟨heL, hxL, hidL, hlamL, ⟨nL, nL', hnL, hnL', hnLm⟩,
      ⟨eL, eL', heLe, heLe', heLm⟩⟩ := Hl
    refine ⟨hid, hidL, by grind, hlamL,
      ⟨[.Call f b₁.nextLam] ++ nL ++ [.Skip], [.Call f b₂.nextLam] ++ nL' ++ [.Skip], ?_, ?_, ?_⟩,
      ⟨eL ++ kappaEdges (callKind Φ f) b₁.nextID enL exL cb₁.nextID,
       eL' ++ kappaEdges (callKind Φ f) b₂.nextID enL' exL' cb₂.nextID, ?_, ?_, ?_⟩⟩
    · rw [hnL]; simp [List.append_assoc]
    · rw [hnL']; simp [List.append_assoc]
    · rw [hnLm]
      simp only [List.map_append, List.map_cons, List.map_nil, NodeKind.shiftLam]
      grind
    · rw [heLe]; simp [List.append_assoc]
    · rw [heLe']; simp [CallGadget.edges, List.append_assoc]
    · rw [heLm]
      simp only [List.map_append, ← kappaEdges_shift]
      grind

/-- The node-kind half of the empty-fragment correspondence.  Lowering from a
builder whose next node is `δ` produces the same node kinds as lowering from
the empty graph, shifted by `δ`, provided both runs use the same lambda-id
offset. -/
theorem lowerStmt_empty_fragment_nodes (Φ : FunEnv) (s : Stmt) (b : BState)
    (δ startLam : Nat) (hid : b.nextID = δ) (hlam : b.nextLam = startLam)
    (hsize : b.cfg.nodes.length = δ) :
    let b₀ : BState := { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
    let (_, b₀') := (lowerStmt Φ s).run b₀
    let (_, b') := (lowerStmt Φ s).run b
    ∀ n k, b₀'.cfg.nodeKind n = some k → b'.cfg.nodeKind (n + δ) = some k := by
  dsimp
  have h := lowerStmt_equivariant Φ s
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam } b δ 0
    (by simpa using hid) (by simpa using hlam)
  obtain ⟨-, -, -, -, ⟨ns₀, ns, hnodes₀, hnodes, hshift⟩, -⟩ := h
  intro n k hn
  simp only [CFG.nodeKind] at hn ⊢
  rw [hnodes₀] at hn
  simp only [List.nil_append] at hn
  rw [hnodes, hshift]
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hn
  rw [← hsize]
  rw [Nat.add_comm n b.cfg.nodes.length,
    List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  simp [hn, NodeKind.shiftLam]
  cases k <;> rfl

/-- The edge half of the empty-fragment correspondence. -/
theorem lowerStmt_empty_fragment_edges_cfg (Φ : FunEnv) (s : Stmt) (b : BState)
    (δ startLam : Nat) (hid : b.nextID = δ) (hlam : b.nextLam = startLam) :
    let b₀ : BState := { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
    let (_, b₀') := (lowerStmt Φ s).run b₀
    let (_, b') := (lowerStmt Φ s).run b
    ∀ e ∈ b₀'.cfg.edges, Edge.shift δ e ∈ b'.cfg.edges := by
  dsimp
  have h := lowerStmt_equivariant Φ s
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam } b δ 0
    (by simpa using hid) (by simpa using hlam)
  obtain ⟨-, -, -, -, -, ⟨es₀, es, hedges₀, hedges, hshift⟩⟩ := h
  intro e he
  rw [hedges₀] at he
  simp only [List.nil_append] at he
  rw [hedges, hshift]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)


theorem cfg_WF (Φ : FunEnv) (s : Stmt) : (Stmt.cfg Φ s).WellFormed := by
  have hspec := lowerStmt_certified Φ s ⟨⟨[], [], 0, 0⟩, 0, 0, []⟩ rfl
  unfold Stmt.cfg
  generalize hrun :
    StateT.run (lowerStmt Φ s) {cfg:={nodes:=[], edges:=[], entry:=0, exit:=0 }, nextID:=0}
      = run_res at *
  rcases run_res with ⟨⟨entry, exit⟩, b'⟩
  simp only at hspec ⊢
  obtain ⟨fragment, hres, hspec⟩ := hspec
  cases hres
  have hes := hspec.edgesAppend
  simp only [List.nil_append] at hes
  refine ⟨hspec.endpointsBounded.1, ?_, ?_, ?_, hspec.endpointsBounded.2⟩
  · intro e he; exact (hspec.edgesBounded e (hes ▸ he)).1
  · intro e he; exact (hspec.edgesBounded e (hes ▸ he)).2
  · intro n hn_len hn_exit
    obtain ⟨n', hn'⟩ := hspec.progress n (Nat.zero_le n)
      (by rw [hspec.stateConsistent]; exact hn_len) hn_exit
    exact ⟨n', hes ▸ hn'⟩

def Stmt.wfcfg (Φ : FunEnv) (s : Stmt) : WFCFG :=
  ⟨Stmt.cfg Φ s, cfg_WF Φ s⟩


@[simp] theorem Stmt.generatedCFGFrom_cfg (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    (s.generatedCFGFrom Φ startLam).cfg = s.cfgFrom Φ startLam := rfl

/-- wellformedness of `Stmt.cfgFrom` Same argument as `cfg_WF`. -/
theorem cfgFrom_WF (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    (Stmt.cfgFrom Φ startLam s).WellFormed := by
  have hspec := lowerStmt_certified Φ s ⟨⟨[], [], 0, 0⟩, 0, startLam, []⟩ rfl
  unfold Stmt.cfgFrom
  generalize hrun :
    StateT.run (lowerStmt Φ s)
      {cfg:={nodes:=[], edges:=[], entry:=0, exit:=0 }, nextID:=0, nextLam := startLam}
      = run_res at *
  rcases run_res with ⟨⟨entry, exit⟩, b'⟩
  simp only at hspec ⊢
  obtain ⟨fragment, hres, hspec⟩ := hspec
  cases hres
  have hes := hspec.edgesAppend
  simp only [List.nil_append] at hes
  refine ⟨hspec.endpointsBounded.1, ?_, ?_, ?_, hspec.endpointsBounded.2⟩
  · intro e he; exact (hspec.edgesBounded e (hes ▸ he)).1
  · intro e he; exact (hspec.edgesBounded e (hes ▸ he)).2
  · intro n hn_len hn_exit
    obtain ⟨n', hn'⟩ := hspec.progress n (Nat.zero_le n)
      (by rw [hspec.stateConsistent]; exact hn_len) hn_exit
    exact ⟨n', hes ▸ hn'⟩

/-
Appending the administrative terminal `Skip` preserves the lowered body
    verbatim and adds exactly that node and the connecting plain edge.
-/
theorem cfgFrom_seq_skip_shape (Φ : FunEnv) (startLam : Nat) (body : Stmt) :
    let g := body.cfgFrom Φ startLam
    (body ;; Stmt.Skip).cfgFrom Φ startLam =
      { nodes := g.nodes ++ [.Skip]
        edges := g.edges ++ [⟨g.exit, g.nodes.length, .plain⟩]
        entry := g.entry
        exit := g.nodes.length } := by
  -- By definition of `Stmt.cfgFrom`, we can unfold the expression for the CFG of `body ;; Skip`.
  simp only [Stmt.cfgFrom];
  apply Eq.symm; exact (by
    have := lowerStmt_spec Φ body { cfg := { nodes := [], edges := [], entry := 0, exit := 0 }, nextID := 0, nextLam := startLam } rfl;
    cases h : StateT.run ( lowerStmt Φ body ) { cfg := { nodes := [], edges := [], entry := 0, exit := 0 }, nextID := 0, nextLam := startLam } ; simp_all +decide [ lowerStmt ] ;
  )

def Stmt.wfcfgFrom (Φ : FunEnv) (startLam : Nat) (s : Stmt) : WFCFG :=
  ⟨Stmt.cfgFrom Φ startLam s, cfgFrom_WF Φ startLam s⟩

/-- Every recorded call certificate has its structural κ-gadget present. -/
def GeneratedCFG.CallCertificatesValid (g : GeneratedCFG) : Prop :=
  ∀ site ∈ g.callGadgets,
    g.cfg.HasKappaGadget site.kappa site.en site.enL site.exL site.ret

theorem Stmt.generatedCFGFrom_callCertificatesValid
    (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    (s.generatedCFGFrom Φ startLam).CallCertificatesValid := by
  have h := lowerStmt_preserves_callCertificates Φ s
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
    (by intro site hsite; simp at hsite)
  simpa [Stmt.generatedCFGFrom, GeneratedCFG.CallCertificatesValid,
    BState.CallCertificatesValid] using h

/-- A generated component with its well-formedness and construction-time
provenance proofs. -/
structure CertifiedGeneratedCFG where
  source : Stmt
  startLam : Nat
  phi : FunEnv
  generated : GeneratedCFG
  wellFormed : generated.cfg.WellFormed
  certificatesValid : generated.CallCertificatesValid
  inlineFragmentsValid : ∀ site ∈ generated.callGadgets,
    generated.cfg.HasInlineBodyFragment phi site

theorem CertifiedGeneratedCFG.gadget_present (component : CertifiedGeneratedCFG)
    {site : CallGadget} (hsite : site ∈ component.generated.callGadgets) :
    component.generated.cfg.HasKappaGadget
      site.kappa site.en site.enL site.exL site.ret :=
  component.certificatesValid site hsite


private theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
private theorem id_map {α β : Type} (f : α → β) (x : Id α) : f <$> x = f x := rfl
private theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

/-- Every lowering begins at the current fresh node.  In particular, the body
of a freshly emitted call begins at the node stored as that call gadget's
`enL`, which is the alignment needed by the inline-fragment certificate. -/
theorem lowerStmt_entry_eq_nextID (Φ : FunEnv) (s : Stmt) (b : BState) :
    ((lowerStmt Φ s).run b).1.1 = b.nextID := by
  induction s generalizing b <;>
    simp [lowerStmt, StateT.run_bind, addNode_run,
      addEdge_run, addCallNodeWithLam_run, addCallGadget_run,
      id_map, id_bind, *]

/-- A freshly lowered call records an inline fragment for its own body.  The
    inherited call-site fragments are handled by `InlineFragmentsValid`; this
    is the new-site case supplied by lowering equivariance. -/
theorem lowerStmt_call_fresh_inlineFragment (Φ : FunEnv) (f : String) (body : Stmt)
    (b : BState) (hinv : b.nextID = b.cfg.nodes.length) :
    let (_, b') := (lowerStmt Φ (.Call f body)).run b
    ∃ site ∈ b'.callGadgets, b'.cfg.HasInlineBodyFragment Φ site := by
  simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addCallNodeWithLam_run,
    addNode_run, addCallGadget_run]
  let b₀ : BState :=
    { cfg := { nodes := b.cfg.nodes ++ [.Call f b.nextLam], edges := b.cfg.edges,
               entry := b.cfg.entry, exit := b.cfg.exit },
      nextID := b.nextID + 1, nextLam := b.nextLam + 1,
      callGadgets := b.callGadgets }
  rcases hbody : StateT.run (lowerStmt Φ body) b₀ with ⟨res, bb⟩
  rcases hstandalone : StateT.run (lowerStmt Φ body)
      { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := b.nextLam + 1 } with
    ⟨standaloneRes, standalone⟩
  let site : CallGadget := ⟨b.nextID, f, b.nextLam, callKind Φ f,
    res.1, res.2, bb.nextID, body⟩
  refine ⟨site, by simp [site], ?_⟩
  have hentry := lowerStmt_entry_eq_nextID Φ body b₀
  rw [hbody] at hentry
  change res.1 = b₀.nextID at hentry
  have hnodes : ∀ n k, (body.generatedCFGFrom Φ (b.nextLam + 1)).cfg.nodeKind n = some k →
      bb.cfg.nodeKind (n + res.1) = some k := by
    rw [hentry]
    have hnodes' := lowerStmt_empty_fragment_nodes Φ body b₀ b₀.nextID b₀.nextLam rfl rfl
      (by simp [b₀, hinv])
    rw [hbody] at hnodes'
    dsimp only [b₀] at hnodes'
    rw [hstandalone] at hnodes'
    simpa [Stmt.generatedCFGFrom, hstandalone] using hnodes'
  have hedges : ∀ e ∈ (body.generatedCFGFrom Φ (b.nextLam + 1)).cfg.edges,
      e.shift res.1 ∈ bb.cfg.edges := by
    rw [hentry]
    have hedges' := lowerStmt_empty_fragment_edges_cfg Φ body b₀ b₀.nextID b₀.nextLam rfl rfl
    rw [hbody] at hedges'
    dsimp only [b₀] at hedges'
    rw [hstandalone] at hedges'
    simpa [Stmt.generatedCFGFrom, hstandalone] using hedges'
  have hfragment : bb.cfg.HasInlineBodyFragment Φ site := by
    constructor
    · simpa [CFG.HasInlineBodyFragment, site] using hedges
    · simpa [CFG.HasInlineBodyFragment, site] using hnodes
  change CFG.HasInlineBodyFragment Φ
    { nodes := bb.cfg.nodes ++ [.Skip], edges := bb.cfg.edges ++ site.edges,
      entry := bb.cfg.entry, exit := bb.cfg.exit } site
  exact CFG.HasInlineBodyFragment.mono hfragment rfl rfl

/-- The fresh inline fragment belongs to the exact gadget emitted by this
    call, rather than merely to some certificate in the output list.  This is
    the new-site branch when packaging fragments into `InlineFragmentsValid`. -/
theorem lowerStmt_call_exact_inlineFragment (Φ : FunEnv) (f : String) (body : Stmt)
    (b : BState) (hinv : b.nextID = b.cfg.nodes.length)
    (enL exL : NodeID) (bb : BState)
    (hbody : StateT.run (lowerStmt Φ body)
      { cfg := { nodes := b.cfg.nodes ++ [.Call f b.nextLam], edges := b.cfg.edges,
                 entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1, nextLam := b.nextLam + 1,
        callGadgets := b.callGadgets } = ((enL, exL), bb)) :
    let (_, b') := (lowerStmt Φ (.Call f body)).run b
    let site : CallGadget := ⟨b.nextID, f, b.nextLam, callKind Φ f, enL, exL, bb.nextID, body⟩
    site ∈ b'.callGadgets ∧ b'.cfg.HasInlineBodyFragment Φ site := by
  simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addCallNodeWithLam_run,
    addNode_run, addCallGadget_run]
  let b₀ : BState :=
    { cfg := { nodes := b.cfg.nodes ++ [.Call f b.nextLam], edges := b.cfg.edges,
               entry := b.cfg.entry, exit := b.cfg.exit },
      nextID := b.nextID + 1, nextLam := b.nextLam + 1,
      callGadgets := b.callGadgets }
  let res : NodeID × NodeID := (enL, exL)
  change StateT.run (lowerStmt Φ body) b₀ = (res, bb) at hbody
  rw [hbody]
  rcases hstandalone : StateT.run (lowerStmt Φ body)
      { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := b.nextLam + 1 } with
    ⟨standaloneRes, standalone⟩
  let site : CallGadget := ⟨b.nextID, f, b.nextLam, callKind Φ f, enL, exL, bb.nextID, body⟩
  refine ⟨?_, ?_⟩
  · simp [res]
  have hentry := lowerStmt_entry_eq_nextID Φ body b₀
  rw [hbody] at hentry
  change res.1 = b₀.nextID at hentry
  have hnodes : ∀ n k, (body.generatedCFGFrom Φ (b.nextLam + 1)).cfg.nodeKind n = some k →
      bb.cfg.nodeKind (n + res.1) = some k := by
    rw [hentry]
    have hnodes' := lowerStmt_empty_fragment_nodes Φ body b₀ b₀.nextID b₀.nextLam rfl rfl
      (by simp [b₀, hinv])
    rw [hbody] at hnodes'
    dsimp only [b₀] at hnodes'
    rw [hstandalone] at hnodes'
    simpa [Stmt.generatedCFGFrom, hstandalone] using hnodes'
  have hedges : ∀ e ∈ (body.generatedCFGFrom Φ (b.nextLam + 1)).cfg.edges,
      e.shift res.1 ∈ bb.cfg.edges := by
    rw [hentry]
    have hedges' := lowerStmt_empty_fragment_edges_cfg Φ body b₀ b₀.nextID b₀.nextLam rfl rfl
    rw [hbody] at hedges'
    dsimp only [b₀] at hedges'
    rw [hstandalone] at hedges'
    simpa [Stmt.generatedCFGFrom, hstandalone] using hedges'
  have hfragment : bb.cfg.HasInlineBodyFragment Φ site := by
    constructor
    · simpa [CFG.HasInlineBodyFragment, site] using hedges
    · simpa [CFG.HasInlineBodyFragment, site] using hnodes
  change CFG.HasInlineBodyFragment Φ
    { nodes := bb.cfg.nodes ++ [.Skip], edges := bb.cfg.edges ++ site.edges,
      entry := bb.cfg.entry, exit := bb.cfg.exit } site
  exact CFG.HasInlineBodyFragment.mono hfragment rfl rfl

/-- Lowering preserves inline-body provenance already recorded in the input
builder, and records matching provenance for every freshly emitted call site. -/
theorem lowerStmt_preserves_inlineFragments (Φ : FunEnv) (s : Stmt) (b : BState)
    (hvalid : b.InlineFragmentsValid Φ) (hinv : b.nextID = b.cfg.nodes.length) :
    let (_, b') := (lowerStmt Φ s).run b
    b'.InlineFragmentsValid Φ := by
  induction s generalizing b with
  | Skip =>
    simpa [lowerStmt] using Builder.addNode_preserves_inlineFragments b .Skip hvalid
  | Decl x e | Assign x e =>
    simpa [lowerStmt] using
      Builder.addNode_preserves_inlineFragments b (.Assign x e) hvalid
  | Invoke =>
    simpa [lowerStmt] using Builder.addNode_preserves_inlineFragments b .Invoke hvalid
  | Seq s₁ s₂ ih₁ ih₂ =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure]
    rcases hfirst : StateT.run (lowerStmt Φ s₁) b with ⟨pair₁, b₁⟩
    have hvalid₁ := ih₁ b hvalid hinv
    rw [hfirst] at hvalid₁
    have hinv₁ := (lowerStmt_spec Φ s₁ b hinv).1
    change (StateT.run (lowerStmt Φ s₁) b).2.nextID =
      (StateT.run (lowerStmt Φ s₁) b).2.cfg.nodes.length at hinv₁
    rw [hfirst] at hinv₁
    rcases hsecond : StateT.run (lowerStmt Φ s₂) b₁ with ⟨pair₂, b₂⟩
    have hvalid₂ := ih₂ b₁ hvalid₁ hinv₁
    rw [hsecond] at hvalid₂
    simpa only [hfirst, hsecond, addEdge_run] using
      Builder.addEdge_preserves_inlineFragments b₂ pair₁.2 pair₂.1 hvalid₂
  | If c t f iht ihf =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run]
    let b₀ : BState :=
      { cfg := { nodes := b.cfg.nodes ++ [.Skip, .Assume c, .Assume (.Not c)],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 3, nextLam := b.nextLam, callGadgets := b.callGadgets }
    have hvalid₀ : b₀.InlineFragmentsValid Φ := by
      simpa [b₀] using
        Builder.addNode_preserves_inlineFragments
          _ (.Assume (.Not c))
          (Builder.addNode_preserves_inlineFragments
            _ (.Assume c) (Builder.addNode_preserves_inlineFragments b .Skip hvalid))
    have hinv₀ : b₀.nextID = b₀.cfg.nodes.length := by
      simp [b₀, hinv]
    rcases ht : StateT.run (lowerStmt Φ t) b₀ with ⟨pairT, bt⟩
    have hvalidT := iht b₀ hvalid₀ hinv₀
    rw [ht] at hvalidT
    have hinvT := (lowerStmt_spec Φ t b₀ hinv₀).1
    change (StateT.run (lowerStmt Φ t) b₀).2.nextID =
      (StateT.run (lowerStmt Φ t) b₀).2.cfg.nodes.length at hinvT
    rw [ht] at hinvT
    rcases hf : StateT.run (lowerStmt Φ f) bt with ⟨pairF, bf⟩
    have hvalidF := ihf bt hvalidT hinvT
    rw [hf] at hvalidF
    have hvalidEx := Builder.addNode_preserves_inlineFragments bf .Skip hvalidF
    have hvalid₁ := Builder.addEdge_preserves_inlineFragments _ (b.nextID) (b.nextID + 1)
      hvalidEx
    have hvalid₂ := Builder.addEdge_preserves_inlineFragments _ (b.nextID) (b.nextID + 2)
      hvalid₁
    have hvalid₃ := Builder.addEdge_preserves_inlineFragments _ (b.nextID + 1) pairT.1
      hvalid₂
    have hvalid₄ := Builder.addEdge_preserves_inlineFragments _ (b.nextID + 2) pairF.1
      hvalid₃
    have hvalid₅ := Builder.addEdge_preserves_inlineFragments _ pairT.2 bf.nextID hvalid₄
    simpa [b₀, ht, hf] using
      Builder.addEdge_preserves_inlineFragments _ pairF.2 bf.nextID hvalid₅
  | While c body ih =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run]
    let b₀ : BState :=
      { cfg := { nodes := b.cfg.nodes ++ [.Skip, .Assume c, .Assume (.Not c)],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 3, nextLam := b.nextLam, callGadgets := b.callGadgets }
    have hvalid₀ : b₀.InlineFragmentsValid Φ := by
      simpa [b₀] using
        Builder.addNode_preserves_inlineFragments
          _ (.Assume (.Not c))
          (Builder.addNode_preserves_inlineFragments
            _ (.Assume c) (Builder.addNode_preserves_inlineFragments b .Skip hvalid))
    have hinv₀ : b₀.nextID = b₀.cfg.nodes.length := by
      simp [b₀, hinv]
    rcases hbody : StateT.run (lowerStmt Φ body) b₀ with ⟨pair, bb⟩
    have hvalidBody := ih b₀ hvalid₀ hinv₀
    rw [hbody] at hvalidBody
    have hvalid₁ := Builder.addEdge_preserves_inlineFragments _ b.nextID (b.nextID + 1)
      hvalidBody
    have hvalid₂ := Builder.addEdge_preserves_inlineFragments _ b.nextID (b.nextID + 2)
      hvalid₁
    have hvalid₃ := Builder.addEdge_preserves_inlineFragments _ (b.nextID + 1) pair.1 hvalid₂
    simpa [b₀, hbody] using
      Builder.addEdge_preserves_inlineFragments _ pair.2 b.nextID hvalid₃
  | Call f body ih =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addCallNodeWithLam_run,
      addNode_run, addCallGadget_run]
    let b₀ : BState :=
      { cfg := { nodes := b.cfg.nodes ++ [.Call f b.nextLam], edges := b.cfg.edges,
                 entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1, nextLam := b.nextLam + 1,
        callGadgets := b.callGadgets }
    have hvalid₀ : b₀.InlineFragmentsValid Φ := by
      simpa [b₀] using Builder.addCallNodeWithLam_preserves_inlineFragments b f hvalid
    have hinv₀ : b₀.nextID = b₀.cfg.nodes.length := by
      simp [b₀, hinv]
    rcases hbody : StateT.run (lowerStmt Φ body) b₀ with ⟨pair, bb⟩
    have hvalidBody := ih b₀ hvalid₀ hinv₀
    rw [hbody] at hvalidBody
    have hvalidRet := Builder.addNode_preserves_inlineFragments bb .Skip hvalidBody
    have hnew := lowerStmt_call_exact_inlineFragment Φ f body b hinv pair.1 pair.2 bb
      (by simpa [b₀] using hbody)
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addCallNodeWithLam_run,
      addNode_run, addCallGadget_run, b₀, hbody] at hnew
    have hvalidRet' :
        ({ cfg := { nodes := bb.cfg.nodes ++ [.Skip], edges := bb.cfg.edges,
                    entry := bb.cfg.entry, exit := bb.cfg.exit },
           nextID := bb.nextID + 1, nextLam := bb.nextLam,
           callGadgets := bb.callGadgets } : BState).InlineFragmentsValid Φ := by
      simpa only [addNode_run] using hvalidRet
    intro site hsite
    simp only [List.mem_append, List.mem_singleton] at hsite
    rcases hsite with hsite | rfl
    · simpa [b₀, hbody] using
        CFG.HasInlineBodyFragment.mono (hvalidRet' site hsite)
          (ns := []) (es := kappaEdges (callKind Φ f) b.nextID pair.1 pair.2 bb.nextID)
          (by simp) rfl
    · simpa [b₀, hbody] using hnew.2

/-- Every call site in a CFG generated from an empty builder has a matching
inline copy of its body fragment. -/
theorem Stmt.generatedCFGFrom_inlineFragmentsValid
    (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    ∀ site ∈ (s.generatedCFGFrom Φ startLam).callGadgets,
      (s.generatedCFGFrom Φ startLam).cfg.HasInlineBodyFragment Φ site := by
  have h := lowerStmt_preserves_inlineFragments Φ s
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
    (by simp [BState.InlineFragmentsValid]) rfl
  simpa [Stmt.generatedCFGFrom, BState.InlineFragmentsValid] using h

def Stmt.certifiedGeneratedCFGFrom (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    CertifiedGeneratedCFG :=
  ⟨s, startLam, Φ, s.generatedCFGFrom Φ startLam, cfgFrom_WF Φ startLam s,
    s.generatedCFGFrom_callCertificatesValid Φ startLam,
    s.generatedCFGFrom_inlineFragmentsValid Φ startLam⟩

def Stmt.certifiedGeneratedCFG (Φ : FunEnv) (s : Stmt) : CertifiedGeneratedCFG :=
  s.certifiedGeneratedCFGFrom Φ 0

/-- The public inline-body provenance guarantee retained by a certified
generated CFG. -/
theorem CertifiedGeneratedCFG.inline_body_fragment (component : CertifiedGeneratedCFG)
    {site : CallGadget} (hsite : site ∈ component.generated.callGadgets) :
    component.generated.cfg.HasInlineBodyFragment component.phi site :=
  component.inlineFragmentsValid site hsite


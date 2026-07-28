import Chartreux.FDuke.Defs
import Chartreux.Analysis.CFG
import Chartreux.Analysis.Generic
import Mathlib.Tactic.Contrapose
import Mathlib.Data.List.Nodup

-- temporary
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

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

/-- distinguish "plain" execution from call summary edges. probably not needed,
    or at least not under this format. -/
inductive EdgeLabel where
| plain
| summary
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

-- # Builder
structure BState where
  cfg : CFG
  nextID : NodeID
  /-- global lambda id, unique for every `call f { s }`. -/
  nextLam : Nat := 0
  /-- Call-site κ-gadgets emitted while constructing `cfg`, in lowering order. -/
  callGadgets : List CallGadget := []
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
    cfg := { s.cfg with edges := s.cfg.edges ++ [⟨src, dst, .plain⟩] } }
def addEdges (es : List Edge) : Builder Unit := do
  modify fun s => { s with
    cfg := { s.cfg with edges := s.cfg.edges ++ es } }
def addCallNode (f : String) : Builder NodeID := do
  let s <- get
  set { s with
        cfg    := { s.cfg with nodes := s.cfg.nodes ++ [NodeKind.Call f s.nextLam] },
        nextID := s.nextID + 1,
        nextLam := s.nextLam + 1 }
  pure s.nextID
def addCallNodeWithLam (f : String) : Builder (NodeID × Nat) := do
  let s <- get
  set { s with
        cfg    := { s.cfg with nodes := s.cfg.nodes ++ [NodeKind.Call f s.nextLam] },
        nextID := s.nextID + 1,
        nextLam := s.nextLam + 1 }
  pure (s.nextID, s.nextLam)
end Builder

/-- funky CFG constructions due to κ. the summary edge is needed to guarantee
    well-formedness and LSteps correctness.

    ε ("no contract") gets the *most permissive* gadget — bypass `en → r` *and*
    back-edge `exL → enL`, i.e. the union of the `+` and `?` shapes (`L*`):
    with no contract every invocation count `k ≥ 0` is possible, so every such
    path must exist on the κ-graph (cf. `UNSOUNDNESS.md`). -/
def kappaEdges (κ : InvKind) (en enL exL r : NodeID) : List Edge :=
  let summary : Edge := ⟨en, r, .summary⟩
  match κ with
  | .none    => [⟨en, enL, .plain⟩, ⟨en, r, .plain⟩, ⟨exL, r, .plain⟩,
                 ⟨exL, enL, .plain⟩, summary]
  | .once    => [⟨en, enL, .plain⟩, ⟨exL, r, .plain⟩, summary]
  | .atLeast => [⟨en, enL, .plain⟩, ⟨exL, r, .plain⟩, ⟨exL, enL, .plain⟩, summary]
  | .atMost  => [⟨en, enL, .plain⟩, ⟨exL, r, .plain⟩, ⟨en, r, .plain⟩, summary]

def CallGadget.edges (g : CallGadget) : List Edge :=
  kappaEdges g.kappa g.en g.enL g.exL g.ret

@[simp] theorem CallGadget.edges_mk (en : NodeID) (f : String) (lamID : Nat)
    (kappa : InvKind) (enL exL ret : NodeID) (body : Stmt) :
    (CallGadget.mk en f lamID kappa enL exL ret body).edges =
      kappaEdges kappa en enL exL ret := rfl

def CallGadget.standaloneRef (site : CallGadget) : CFGRef := .lam site.lamID

def CallGadget.standaloneStartLam (site : CallGadget) : Nat := site.lamID + 1

def CallGadget.standaloneStmt (site : CallGadget) : Stmt := site.body ;; .Skip

namespace Builder
def addCallGadget (site : CallGadget) : Builder Unit := do
  modify fun s => { s with
    cfg := { s.cfg with edges := s.cfg.edges ++ site.edges },
    callGadgets := s.callGadgets ++ [site] }
end Builder

theorem kappaEdges_en_enL (κ : InvKind) (en enL exL r : NodeID) :
    (⟨en, enL, .plain⟩ : Edge) ∈ kappaEdges κ en enL exL r := by
  cases κ <;> simp [kappaEdges]

theorem kappaEdges_exL_r (κ : InvKind) (en enL exL r : NodeID) :
    (⟨exL, r, .plain⟩ : Edge) ∈ kappaEdges κ en enL exL r := by
  cases κ <;> simp [kappaEdges]

theorem kappaEdges_mem (κ : InvKind) (en enL exL r : NodeID) (e : Edge)
    (he : e ∈ kappaEdges κ en enL exL r) :
    (e.src = en ∨ e.src = exL) ∧ (e.dst = enL ∨ e.dst = r) := by
  cases κ <;>
    simp only [kappaEdges, List.mem_cons, List.not_mem_nil, or_false] at he <;>
    grind

theorem kappaEdges_summary (κ : InvKind) (en enL exL r : NodeID) (e : Edge)
    (he : e ∈ kappaEdges κ en enL exL r) (hk : e.kind = .summary) :
    e = ⟨en, r, .summary⟩ := by
  cases κ <;>
    simp only [kappaEdges, List.mem_cons, List.not_mem_nil, or_false] at he <;>
    grind

/-- Every call-site gadget contains its summary edge. -/
theorem kappaEdges_summary_mem (κ : InvKind) (en enL exL r : NodeID) :
    (⟨en, r, .summary⟩ : Edge) ∈ kappaEdges κ en enL exL r := by
  cases κ <;> simp [kappaEdges]

/-- The target of a summary edge in one κ-gadget is its return node. -/
theorem kappaEdges_summary_target (κ : InvKind) (en enL exL r : NodeID) (e : Edge)
    (he : e ∈ kappaEdges κ en enL exL r) (hk : e.kind = .summary) :
    e.dst = r := by
  rw [kappaEdges_summary κ en enL exL r e he hk]

/-- A graph contains the complete κ-gadget for the specified call-site nodes. -/
def CFG.HasKappaGadget (g : CFG) (κ : InvKind) (en enL exL r : NodeID) : Prop :=
  ∀ ⦃e⦄, e ∈ kappaEdges κ en enL exL r → e ∈ g.edges

/-- A graph with a complete κ-gadget contains that gadget's summary edge. -/
theorem CFG.HasKappaGadget.summary_mem {g : CFG} {κ : InvKind} {en enL exL r : NodeID}
    (hg : g.HasKappaGadget κ en enL exL r) :
    (⟨en, r, .summary⟩ : Edge) ∈ g.edges :=
  hg (kappaEdges_summary_mem κ en enL exL r)

/-- A complete κ-gadget has exactly one summary target at its call-site node. -/
theorem CFG.HasKappaGadget.summary_target_unique {g : CFG} {κ : InvKind} {en enL exL r : NodeID}
    (_ : g.HasKappaGadget κ en enL exL r) {e₁ e₂ : Edge}
    (he₁ : e₁ ∈ kappaEdges κ en enL exL r) (hk₁ : e₁.kind = .summary)
    (he₂ : e₂ ∈ kappaEdges κ en enL exL r) (hk₂ : e₂.kind = .summary) :
    e₁.src = e₂.src → e₁.dst = e₂.dst := by
  intro _
  rw [kappaEdges_summary κ en enL exL r e₁ he₁ hk₁,
    kappaEdges_summary κ en enL exL r e₂ he₂ hk₂]

/-- All construction-time call certificates retained by a builder are present
in its current graph. -/
def BState.CallGadgetsValid (s : BState) : Prop :=
  ∀ site ∈ s.callGadgets,
    s.cfg.HasKappaGadget site.kappa site.en site.enL site.exL site.ret

/-- A complete κ-gadget has a unique summary target amongst all of its emitted
edges. This formulation is convenient when the gadget is known as a sublist of
the fragment emitted by `lowerStmt`. -/
theorem kappaEdges_summary_target_unique (κ : InvKind) (en enL exL r : NodeID)
    {e₁ e₂ : Edge} (he₁ : e₁ ∈ kappaEdges κ en enL exL r)
    (hk₁ : e₁.kind = .summary) (he₂ : e₂ ∈ kappaEdges κ en enL exL r)
    (hk₂ : e₂.kind = .summary) : e₁.src = e₂.src → e₁.dst = e₂.dst := by
  intro _
  rw [kappaEdges_summary κ en enL exL r e₁ he₁ hk₁,
    kappaEdges_summary κ en enL exL r e₂ he₂ hk₂]

/-- The invocation kind of a `call f { s }` site: `Φ.lookup f`'s kind, defaulting
    to `ε` (`none`) when `f ∉ dom(Φ)`. -/
def callKind (Φ : FunEnv) (f : String) : InvKind :=
  ((Φ.lookup f).map (·.1)).getD .none

open Builder
def lowerStmt (Φ : FunEnv) : Stmt -> Builder (NodeID × NodeID)
| .Skip => do
    let n <- addNode (.Skip)
    pure (n, n)
| .Decl x e | .Assign x e => do
    let n <- addNode (.Assign x e)
    pure (n, n)
| .Seq s₁ s₂ => do
    let (en₁, ex₁) <- lowerStmt Φ s₁
    let (en₂, ex₂) <- lowerStmt Φ s₂
    addEdge ex₁ en₂
    pure (en₁, ex₂)
| .If c t f => do
    let en <- addNode (.Skip) -- could probably be something in relation to c
    let atru <- addNode (.Assume c)
    let afls <- addNode (.Assume (.Not c))
    let (ent, ext) <- lowerStmt Φ t
    let (enf, exf) <- lowerStmt Φ f
    let ex <- addNode (.Skip)
    addEdge en atru; addEdge en afls
    addEdge atru ent; addEdge afls enf
    addEdge ext ex; addEdge exf ex
    pure (en, ex)
| .While c b => do
    let en <- addNode (.Skip) -- could probably be something in relation to c
    let atru <- addNode (.Assume c)
    let afls <- addNode (.Assume (.Not c))
    let (enb, exb) <- lowerStmt Φ b
    addEdge en atru; addEdge en afls
    addEdge atru enb
    addEdge exb en
    pure (en, afls)
| .Invoke => do
    let n <- addNode (.Invoke)
    pure (n, n)
| .Call f lam => do
    let (en, lamID) <- addCallNodeWithLam f
    let (enL, exL) <- lowerStmt Φ lam
    let r <- addNode (.Skip)
    addCallGadget ⟨en, f, lamID, callKind Φ f, enL, exL, r, lam⟩
    pure (en, r)

def Stmt.cfg (Φ : FunEnv) (s : Stmt) : CFG :=
    let (res, st) := (lowerStmt Φ s).run { cfg := ⟨[], [], 0, 0⟩, nextID := 0 }
    { st.cfg with entry := res.1, exit := res.2 }

/-- A CFG together with the construction-time call certificates from its
lowering run. `Stmt.cfg` remains the projection used by existing consumers. -/
structure GeneratedCFG where
  cfg : CFG
  callGadgets : List CallGadget

/-- Build a certificate-bearing CFG for `s`, allocating call-site lambda ids
starting at `startLam`.  This is the generated counterpart of `cfgFrom`. -/
def Stmt.generatedCFGFrom (Φ : FunEnv) (startLam : Nat) (s : Stmt) : GeneratedCFG :=
  let (res, st) := (lowerStmt Φ s).run
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
  ⟨{ st.cfg with entry := res.1, exit := res.2 }, st.callGadgets⟩

def Stmt.generatedCFG (Φ : FunEnv) (s : Stmt) : GeneratedCFG :=
  s.generatedCFGFrom Φ 0

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

/-- Besides being present, every summary edge of a builder state is accounted
for by one of its construction-time call certificates. -/
def BState.CallCertificatesValid (s : BState) : Prop :=
  s.CallGadgetsValid ∧
    ∀ e ∈ s.cfg.edges, e.kind = .summary →
      ∃ site ∈ s.callGadgets, e ∈ site.edges

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
  intro b ⟨hgadgets, hsummary⟩
  constructor
  · exact Builder.addNode_preserves_callGadgetsValid b k hgadgets
  · intro e he hk
    exact hsummary e he hk

theorem Builder.addEdge_preserves_callCertificates (src dst : NodeID) :
    (Builder.addEdge src dst).PreservesCallCertificates := by
  intro b ⟨hgadgets, hsummary⟩
  constructor
  · exact Builder.addEdge_preserves_callGadgetsValid b src dst hgadgets
  · intro e he hk
    simp only [addEdge_run, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hsummary e he hk
    · simp at hk

theorem Builder.addCallNodeWithLam_preserves_callCertificates (f : String) :
    (Builder.addCallNodeWithLam f).PreservesCallCertificates := by
  intro b ⟨hgadgets, hsummary⟩
  constructor
  · exact Builder.addCallNodeWithLam_preserves_callGadgetsValid b f hgadgets
  · intro e he hk
    exact hsummary e he hk

theorem Builder.addCallGadget_preserves_callCertificates (site : CallGadget) :
    (Builder.addCallGadget site).PreservesCallCertificates := by
  intro b ⟨hgadgets, hsummary⟩
  constructor
  · exact Builder.addCallGadget_preserves_callGadgetsValid b site hgadgets
  · intro e he hk
    simp only [addCallGadget_run, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨old, hold, heold⟩ := hsummary e he hk
      exact ⟨old, List.mem_append_left _ hold, heold⟩
    · exact ⟨site, List.mem_append_right _ (List.mem_singleton_self _), he⟩

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

/-- The summary edge emitted for a directly lowered call has the exact
construction-time certificate as a witness in the output state. -/
theorem lowerStmt_call_summary_has_record (Φ : FunEnv) (f : String) (lam : Stmt) (b : BState) :
    let (_, b') := (lowerStmt Φ (.Call f lam)).run b
    ∃ enL exL ret,
      let site : CallGadget := ⟨b.nextID, f, b.nextLam, callKind Φ f, enL, exL, ret, lam⟩
      site ∈ b'.callGadgets ∧ (⟨site.en, site.ret, .summary⟩ : Edge) ∈ b'.cfg.edges := by
  simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addCallNodeWithLam_run,
    addNode_run, addCallGadget_run]
  rcases hrun : StateT.run (lowerStmt Φ lam)
      { cfg := { b.cfg with nodes := b.cfg.nodes ++ [.Call f b.nextLam] },
        nextID := b.nextID + 1, nextLam := b.nextLam + 1,
        callGadgets := b.callGadgets } with ⟨⟨enL, exL⟩, bl⟩
  refine ⟨enL, exL, bl.nextID, ?_, ?_⟩
  · simp
  · simp [CallGadget.edges, kappaEdges_summary_mem]

/-- The generated CFG of a call exposes the certificate witnessing its root
summary edge. Nested calls are retained in the same `callGadgets` list. -/
theorem Stmt.generatedCFG_call_summary_has_record (Φ : FunEnv) (f : String) (lam : Stmt) :
    ∃ enL exL ret,
      let site : CallGadget := ⟨0, f, 0, callKind Φ f, enL, exL, ret, lam⟩
      site ∈ ((.Call f lam : Stmt).generatedCFG Φ).callGadgets ∧
      (⟨site.en, site.ret, .summary⟩ : Edge) ∈ ((.Call f lam : Stmt).generatedCFG Φ).cfg.edges := by
  simpa [Stmt.generatedCFG] using
    (lowerStmt_call_summary_has_record Φ f lam
      { cfg := ⟨[], [], 0, 0⟩, nextID := 0 })

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


set_option maxHeartbeats 1600000 in
-- well formedness invariant. needs additional heartbeats cause everything sucks.
theorem lowerStmt_spec (Φ : FunEnv) (s : Stmt) (b : BState)
    (hinv : b.nextID = b.cfg.nodes.length) :
    let (res, b') := (lowerStmt Φ s).run b
    b'.nextID = b'.cfg.nodes.length ∧
    (∃ ns, b'.cfg.nodes = b.cfg.nodes ++ ns) ∧
    (∃ es, b'.cfg.edges = b.cfg.edges ++ es ∧
      (∀ e ∈ es, e.src < b'.cfg.nodes.length ∧
        e.dst < b'.cfg.nodes.length) ∧
      (∀ n, b.nextID ≤ n → n < b'.nextID → n ≠ res.2 →
        ∃ n', (⟨n, n', .plain⟩ : Edge) ∈ es) ∧
      (∀ e ∈ es, e.kind = .summary →
        ∃ f ℓ, b'.cfg.nodes[e.src]? = some (.Call f ℓ))) ∧
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
    obtain ⟨hinvb, ⟨nsb, hnsb⟩, ⟨esb, hesb, hbb, hedb, hsumb⟩, henL, hexL⟩ := hbody
    -- abbreviations: `en = b.nextID` is the call node, `r = bb.nextID` the return node
    have hmono : b.nextID + 1 ≤ bb.nextID := by rw [hinvb, hnsb]; simp; grind
    have hlen : bb.nextID = bb.cfg.nodes.length := hinvb
    refine ⟨by simp [hinvb], ?_, ?_, by simp; grind, by simp; grind⟩
    · exact ⟨[NodeKind.Call f b.nextLam] ++ nsb ++ [NodeKind.Skip],
        by rw [hnsb]; simp [List.append_assoc]⟩
    · refine ⟨esb ++ kappaEdges (callKind Φ f) b.nextID enL exL bb.nextID,
        by rw [hesb]; simp [CallGadget.edges, List.append_assoc], ?_⟩
      refine ⟨?_, ?_, ?_⟩
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
      · intro e he hk
        simp only [List.mem_append] at he
        rcases he with he | he
        · obtain ⟨f', ℓ', hcall⟩ := hsumb e he hk
          exact ⟨f', ℓ', by
            rw [List.getElem?_append_left (hbb e he).1]; exact hcall⟩
        · have hesum := kappaEdges_summary _ _ _ _ _ _ he hk
          subst hesum
          refine ⟨f, b.nextLam, ?_⟩
          rw [hnsb, hinv]
          simp
  | Seq s₁ s₂ ih₁ ih₂ =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure]
    rcases hr₁ : StateT.run (lowerStmt Φ s₁) b with ⟨⟨en₁, ex₁⟩, b₁⟩
    have h₁ := ih₁ b hinv
    rw [hr₁] at h₁
    simp only at h₁
    obtain ⟨hinv₁, ⟨ns₁, hns₁⟩, ⟨es₁, hes₁, hb₁, hedge₁, hsum₁⟩, hen₁, hex₁⟩ := h₁
    rcases hr₂ : StateT.run (lowerStmt Φ s₂) b₁ with ⟨⟨en₂, ex₂⟩, b₂⟩
    have h₂ := ih₂ b₁ hinv₁
    rw [hr₂] at h₂
    simp only at h₂
    obtain ⟨hinv₂, ⟨ns₂, hns₂⟩, ⟨es₂, hes₂, hb₂, hedge₂, hsum₂⟩, hen₂, hex₂⟩ := h₂
    simp only [addEdge_run]
    have hmono : b₁.cfg.nodes.length ≤ b₂.cfg.nodes.length := by rw [hns₂]; simp
    refine ⟨by simpa using hinv₂, ⟨ns₁ ++ ns₂, by rw [hns₂, hns₁]; simp⟩,
      ⟨es₁ ++ es₂ ++ [⟨ex₁, en₂, .plain⟩], by simp [hes₂, hes₁, List.append_assoc], ?_⟩,
      by grind, by simpa using hex₂⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with (he | he) | he
      · exact ⟨by have := (hb₁ e he).1; simp; grind, by have := (hb₁ e he).2; simp; grind⟩
      · have := hb₂ e he; simpa using this
      · subst he; exact ⟨by simp; grind, by simpa using hen₂⟩
    · grind
    · intro e he hk
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with (he | he) | he
      · obtain ⟨f, ℓ, h⟩ := hsum₁ e he hk
        exact ⟨f, ℓ, by rw [hns₂, List.getElem?_append_left (hb₁ e he).1]; exact h⟩
      · exact hsum₂ e he hk
      · subst he; simp at hk
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
    obtain ⟨hinvt, ⟨nst, hnst⟩, ⟨est, hest, hbt, hedt, hsumt⟩, hent, hext⟩ := ht
    have hf := ih_f bt hinvt
    rcases hrf : StateT.run (lowerStmt Φ f) bt with ⟨⟨enf, exf⟩, bf⟩
    rw [hrf] at hf
    simp only at hf
    obtain ⟨hinvf, ⟨nsf, hnsf⟩, ⟨esf, hesf, hbf, hedf, hsumf⟩, henf, hexf⟩ := hf
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
      refine ⟨?_, ?_, ?_⟩
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
      · intro e he hk
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with (he | he) | he
        · obtain ⟨f', ℓ', h⟩ := hsumt e he hk
          have h1 : e.src < bt.cfg.nodes.length := (hbt e he).1
          exact ⟨f', ℓ', by
            rw [List.getElem?_append_left (Nat.lt_of_lt_of_le h1 hL2), hnsf,
              List.getElem?_append_left h1]
            exact h⟩
        · obtain ⟨f', ℓ', h⟩ := hsumf e he hk
          exact ⟨f', ℓ', by
            rw [List.getElem?_append_left (hbf e he).1]; exact h⟩
        · rcases he with h|h|h|h|h|h <;> subst h <;> simp at hk
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
    obtain ⟨hinvb, ⟨nsb, hnsb⟩, ⟨esb, hesb, hbb, hedb, hsumb⟩, henb, hexb⟩ := hb
    have hL1 : b.cfg.nodes.length + 3 ≤ bb.cfg.nodes.length := by
      rw [hnsb]; grind
    refine ⟨by simp [hinvb], ?_, ?_, by simp; grind, by simp; grind⟩
    · exact ⟨[NodeKind.Skip, NodeKind.Assume c, NodeKind.Assume c.Not] ++ nsb,
        by rw [hnsb]; simp [List.append_assoc]⟩
    · refine ⟨esb ++ [⟨b.nextID, b.nextID + 1, .plain⟩, ⟨b.nextID, b.nextID + 1 + 1, .plain⟩,
        ⟨b.nextID + 1, enb, .plain⟩, ⟨exb, b.nextID, .plain⟩],
        by rw [hesb]; simp [List.append_assoc], ?_⟩
      refine ⟨?_, ?_, ?_⟩
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
      · intro e he hk
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with he | he
        · exact hsumb e he hk
        · rcases he with h|h|h|h <;> subst h <;> simp at hk

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
  obtain ⟨-, -, ⟨es, hes, -, -, -⟩, -, -⟩ := hspec
  refine ⟨enL, exL, bl.nextID,
    es ++ kappaEdges (callKind Φ f) b.nextID enL exL bl.nextID, rfl, ?_, ?_⟩
  · rw [hes]
    simp [CallGadget.edges, List.append_assoc]
  · intro e he
    exact List.mem_append_right _ he

/-- The append-relative call-site fact, stated for an arbitrary statement and
    proved by structural induction.  The non-call cases are impossible under
    `hroot`; the call case exposes both the whole freshly appended κ-gadget and
    the fact that its summary edges have one return target.  Keeping the
    initial graph explicit is important: callers may lower into a nonempty
    builder while reasoning only about the fragment they append. -/
theorem lowerStmt_root_call_gadget (Φ : FunEnv) (s : Stmt) (b : BState)
    (hinv : b.nextID = b.cfg.nodes.length) {f : String} {lam : Stmt}
    (hroot : s = .Call f lam) :
    let (res, b') := (lowerStmt Φ s).run b
    ∃ enL exL r es, res = (b.nextID, r) ∧ b'.cfg.edges = b.cfg.edges ++ es ∧
      b'.cfg.HasKappaGadget (callKind Φ f) b.nextID enL exL r ∧
      (∀ ⦃e₁ e₂⦄, e₁ ∈ kappaEdges (callKind Φ f) b.nextID enL exL r →
        e₁.kind = .summary → e₂ ∈ kappaEdges (callKind Φ f) b.nextID enL exL r →
        e₂.kind = .summary → e₁.dst = e₂.dst) := by
  induction s generalizing b with
  | Skip | Decl | Assign | Seq | If | While | Invoke => cases hroot
  | Call g body ih =>
    cases hroot
    obtain ⟨enL, exL, r, es, hres, hedges, hgadget⟩ :=
      lowerStmt_call_gadget_fragment Φ f lam b hinv
    refine ⟨enL, exL, r, es, hres, hedges, ?_, ?_⟩
    · intro e he
      rw [hedges]
      exact List.mem_append_right _ (hgadget he)
    · intro e₁ e₂ he₁ hk₁ he₂ hk₂
      rw [kappaEdges_summary_target _ _ _ _ _ e₁ he₁ hk₁,
        kappaEdges_summary_target _ _ _ _ _ e₂ he₂ hk₂]


-- # Builder equivariance: `lowerStmt` output shifts uniformly with the offsets

/-- Shift both endpoints of an edge by `δ`. Used to relate a lowered fragment
    to a copy of it emitted at a `nextID` offset `δ` higher. -/
def Edge.shift (δ : NodeID) (e : Edge) : Edge := ⟨e.src + δ, e.dst + δ, e.kind⟩

/-- Shift the lambda id of a `Call` node by `δL`, leaving every other node
    kind untouched. A `Call` node's `ℓ` is the only node payload that depends
    on the builder's `nextLam`, so this is exactly how a node list changes when
    the same statement is lowered at a higher `nextLam` offset. -/
def NodeKind.shiftLam (δL : Nat) : NodeKind → NodeKind
  | .Call f ℓ => .Call f (ℓ + δL)
  | k => k

/-- The inline copy of a call body's standalone lowering, as it occurs in a
larger CFG.  Lambda identifiers agree because both lowerings start immediately
after the call site's own identifier; only node identifiers are shifted. -/
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

set_option maxHeartbeats 1600000 in
-- The proof is a *doubled* state-monad induction over `Stmt` (it runs `lowerStmt`
-- from two states at once and matches the fragments), so it needs the same
-- raised heartbeat budget as `lowerStmt_spec`.
/-- **Builder equivariance for `lowerStmt`.** Running
    `lowerStmt Φ s` from two builder states that differ only by a `nextID`
    offset `δ` and a `nextLam` offset `δL` produces the *same* CFG fragment up
    to those two shifts: the returned entry/exit ids and the resulting
    `nextID`/`nextLam` shift by `δ`/`δL`, the appended nodes agree after
    `NodeKind.shiftLam δL` (only the lambda id of each nested `call` moves), and
    the appended edges agree after `Edge.shift δ`. This is the structural fact
    that lets the inlined copy of a lambda body inside a caller be identified
    with the lambda's standalone CFG (built at a different offset), which any
    proof of `Chartreux.FDuke.Refinement`'s projection obligation (`cek_projection`)
    will need to transport lam-body CEK runs onto the caller's inline copy. -/
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

def CFG.WellFormed (g : CFG) :=
  (g.entry < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.src < g.nodes.length) ∧
  (∀ e ∈ g.edges, e.dst < g.nodes.length) ∧
  (∀ n < g.nodes.length, n ≠ g.exit → ∃ n', (⟨n, n', .plain⟩ : Edge) ∈ g.edges) ∧
  (∀ e ∈ g.edges, e.kind = .summary → ∃ f ℓ, g.nodeKind e.src = some (.Call f ℓ)) ∧
  (g.exit < g.nodes.length)

theorem cfg_WF (Φ : FunEnv) (s : Stmt) : (Stmt.cfg Φ s).WellFormed := by
  have hspec := lowerStmt_spec Φ s ⟨⟨[], [], 0, 0⟩, 0, 0, []⟩ rfl
  unfold Stmt.cfg
  generalize hrun :
    StateT.run (lowerStmt Φ s) {cfg:={nodes:=[], edges:=[], entry:=0, exit:=0 }, nextID:=0}
      = run_res at *
  obtain ⟨hlen, -, ⟨es, hes, hbound, hedge, hsum⟩, hen, hexit⟩ := hspec
  simp only [List.nil_append] at hes
  refine ⟨hen, ?_, ?_, ?_, ?_, hexit⟩
  · intro e he; exact (hbound e (hes ▸ he)).1
  · intro e he; exact (hbound e (hes ▸ he)).2
  · intro n hn_len hn_exit
    obtain ⟨n', hn'⟩ := hedge n (Nat.zero_le n) (by grind) hn_exit
    exact ⟨n', hes ▸ hn'⟩
  · intro e he hk; exact hsum e (hes ▸ he) hk

abbrev WFCFG := { cfg : CFG // cfg.WellFormed }

def Stmt.wfcfg (Φ : FunEnv) (s : Stmt) : WFCFG :=
  ⟨Stmt.cfg Φ s, cfg_WF Φ s⟩

/-- build cfg for `s` starting from lambda id `startLam`. -/
def Stmt.cfgFrom (Φ : FunEnv) (startLam : Nat) (s : Stmt) : CFG :=
    let (res, st) := (lowerStmt Φ s).run { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
    { st.cfg with entry := res.1, exit := res.2 }

@[simp] theorem Stmt.generatedCFGFrom_cfg (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    (s.generatedCFGFrom Φ startLam).cfg = s.cfgFrom Φ startLam := rfl

/-- wellformedness of `Stmt.cfgFrom` Same argument as `cfg_WF`. -/
theorem cfgFrom_WF (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    (Stmt.cfgFrom Φ startLam s).WellFormed := by
  have hspec := lowerStmt_spec Φ s ⟨⟨[], [], 0, 0⟩, 0, startLam, []⟩ rfl
  unfold Stmt.cfgFrom
  generalize hrun :
    StateT.run (lowerStmt Φ s)
      {cfg:={nodes:=[], edges:=[], entry:=0, exit:=0 }, nextID:=0, nextLam := startLam}
      = run_res at *
  obtain ⟨hlen, -, ⟨es, hes, hbound, hedge, hsum⟩, hen, hexit⟩ := hspec
  simp only [List.nil_append] at hes
  refine ⟨hen, ?_, ?_, ?_, ?_, hexit⟩
  · intro e he; exact (hbound e (hes ▸ he)).1
  · intro e he; exact (hbound e (hes ▸ he)).2
  · intro n hn_len hn_exit
    obtain ⟨n', hn'⟩ := hedge n (Nat.zero_le n) (by grind) hn_exit
    exact ⟨n', hes ▸ hn'⟩
  · intro e he hk; exact hsum e (hes ▸ he) hk

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

/-- The provenance guarantees retained with a generated CFG: every recorded
κ-gadget is present, and every summary edge is explained by a record. -/
def GeneratedCFG.CallCertificatesValid (g : GeneratedCFG) : Prop :=
  (∀ site ∈ g.callGadgets,
    g.cfg.HasKappaGadget site.kappa site.en site.enL site.exL site.ret) ∧
  (∀ e ∈ g.cfg.edges, e.kind = .summary →
    ∃ site ∈ g.callGadgets, e ∈ site.edges)

theorem Stmt.generatedCFGFrom_callCertificatesValid
    (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    (s.generatedCFGFrom Φ startLam).CallCertificatesValid := by
  have h := lowerStmt_preserves_callCertificates Φ s
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
    (by
      constructor
      · intro site hsite
        simp at hsite
      · intro e he
        simp at he)
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
  component.certificatesValid.1 site hsite

theorem CertifiedGeneratedCFG.summary_has_gadget (component : CertifiedGeneratedCFG)
    {e : Edge} (he : e ∈ component.generated.cfg.edges) (hk : e.kind = .summary) :
    ∃ site ∈ component.generated.callGadgets, e ∈ site.edges :=
  component.certificatesValid.2 e he hk

/-- A summary edge recorded by one component certificate has that certificate's
return node as target. -/
theorem CertifiedGeneratedCFG.summary_target (component : CertifiedGeneratedCFG)
    {site : CallGadget} (_hsite : site ∈ component.generated.callGadgets)
    {e : Edge} (he : e ∈ site.edges) (hk : e.kind = .summary) : e.dst = site.ret := by
  exact kappaEdges_summary_target site.kappa site.en site.enL site.exL site.ret e he hk

/-- Summary targets are unique within the κ-gadget witnessed by a generated
component certificate. This is intentionally a generated-component fact,
rather than a property claimed for arbitrary well-formed CFGs. -/
theorem CertifiedGeneratedCFG.summary_target_unique (component : CertifiedGeneratedCFG)
    {site : CallGadget} (hsite : site ∈ component.generated.callGadgets)
    {e₁ e₂ : Edge} (he₁ : e₁ ∈ site.edges) (hk₁ : e₁.kind = .summary)
    (he₂ : e₂ ∈ site.edges) (hk₂ : e₂.kind = .summary) : e₁.dst = e₂.dst := by
  rw [component.summary_target hsite he₁ hk₁, component.summary_target hsite he₂ hk₂]

/-- collect all occurrences of lambda bodies. -/
def collectLams : Stmt → StateM Nat (List (Nat × Stmt))
  | .Seq s₁ s₂  => do let a ← collectLams s₁; let b ← collectLams s₂; pure (a ++ b)
  | .If _ t f   => do let a ← collectLams t;  let b ← collectLams f;  pure (a ++ b)
  | .While _ b  => collectLams b
  | .Call _ body => do
      let ℓ ← modifyGet (fun n => (n, n + 1))
      let rest ← collectLams body
      pure ((ℓ, body) :: rest)
  | _ => pure []

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

-- temporary
set_option linter.flexible false in
/-- `collectLams` allocates consecutive identifiers, starting at its input
counter. -/
theorem collectLams_allocation (s : Stmt) : ∀ start : Nat,
    let out := (collectLams s).run start
    out.2 = start + out.1.length ∧
      out.1.map Prod.fst = List.range' start out.1.length := by
  intro start
  induction s generalizing start <;>
    simp [collectLams, StateT.run_bind, StateT.run_pure, id_bind, id_map, id_pure,
      *, Nat.add_assoc, Nat.add_comm]
  rw [Nat.add_comm 1, List.range'_succ]

/-- The collector advances its counter by exactly the number of lambda bodies
it reports. -/
theorem collectLams_end_eq_start_add_length (s : Stmt) (start : Nat) :
    ((collectLams s).run start).2 = start + ((collectLams s).run start).1.length :=
  (collectLams_allocation s start).1

/-- The lambda identifiers emitted by one collector run are pairwise distinct. -/
theorem collectLams_ids_nodup (s : Stmt) (start : Nat) :
    (((collectLams s).run start).1.map Prod.fst).Nodup := by
  rw [(collectLams_allocation s start).2]
  exact List.nodup_range' 1

/-- Every identifier emitted by a collector run lies in the half-open interval
from the input counter to the resulting counter. -/
theorem collectLams_id_mem_bounds (s : Stmt) (start : Nat) {ℓ : Nat}
    (hℓ : ℓ ∈ ((collectLams s).run start).1.map Prod.fst) :
    start ≤ ℓ ∧ ℓ < ((collectLams s).run start).2 := by
  rw [(collectLams_allocation s start).2] at hℓ
  rw [List.mem_range'_1] at hℓ
  simpa [collectLams_end_eq_start_add_length] using hℓ

/-- Pair membership in collector output exposes the corresponding allocation
interval directly. -/
theorem collectLams_pair_mem_bounds (s : Stmt) (start : Nat) {ℓ : Nat} {body : Stmt}
    (hpair : (ℓ, body) ∈ ((collectLams s).run start).1) :
    start ≤ ℓ ∧ ℓ < ((collectLams s).run start).2 :=
  collectLams_id_mem_bounds s start (List.mem_map_of_mem hpair)

/-- Two collector runs threaded through their counters allocate disjoint,
collectively unique identifier sequences. This is the composition fact needed
when a program family is assembled by a fold. -/
theorem collectLams_threaded_ids_nodup (s₁ s₂ : Stmt) (start : Nat) :
    (((collectLams s₁).run start).1.map Prod.fst ++
      ((collectLams s₂).run ((collectLams s₁).run start).2).1.map Prod.fst).Nodup := by
  rw [(collectLams_allocation s₁ start).2,
    (collectLams_allocation s₂ ((collectLams s₁).run start).2).2,
    collectLams_end_eq_start_add_length]
  rw [show List.range' start ((collectLams s₁).run start).1.length ++
      List.range' (start + ((collectLams s₁).run start).1.length)
        ((collectLams s₂).run
          (start + ((collectLams s₁).run start).1.length)).1.length =
      List.range' start (((collectLams s₁).run start).1.length +
        ((collectLams s₂).run
          (start + ((collectLams s₁).run start).1.length)).1.length) by
        simpa using (List.range'_append (s := start)
          (m := ((collectLams s₁).run start).1.length)
          (n := ((collectLams s₂).run
            (start + ((collectLams s₁).run start).1.length)).1.length) (step := 1))]
  exact List.nodup_range' 1

/-- The identifiers from two threaded collector runs are disjoint. -/
theorem collectLams_threaded_ids_disjoint (s₁ s₂ : Stmt) (start : Nat) :
    (((collectLams s₁).run start).1.map Prod.fst).Disjoint
      (((collectLams s₂).run ((collectLams s₁).run start).2).1.map Prod.fst) :=
  List.disjoint_of_nodup_append (collectLams_threaded_ids_nodup s₁ s₂ start)

/-- Lowering consumes lambda identifiers in precisely the order reported by
`collectLams`.  The statement is append-relative so it also applies while a
component is being built inside a larger lowering run. -/
theorem lowerStmt_callGadgets_collectLams (Φ : FunEnv) (s : Stmt) :
    ∀ b : BState,
      let b' := ((lowerStmt Φ s).run b).2
      b'.nextLam = ((collectLams s).run b.nextLam).2 ∧
      ∀ site ∈ b'.callGadgets, site ∈ b.callGadgets ∨
        (site.lamID, site.body) ∈ ((collectLams s).run b.nextLam).1 := by
  intro b
  induction s generalizing b <;>
    simp [lowerStmt, collectLams, Builder.addNode, Builder.addEdge,
      Builder.addCallNodeWithLam, Builder.addCallGadget, id_bind, id_map, id_pure,
      *, List.append_assoc]
  all_goals grind
  /-
  intro b
  induction s generalizing b with
  | Skip | Decl | Assign | Invoke =>
    change b.nextLam = b.nextLam ∧
      b.callGadgets.map (fun site => (site.lamID, site.body)) =
        b.callGadgets.map (fun site => (site.lamID, site.body)) ++ []
    simp
  | Seq s₁ s₂ ih₁ ih₂ =>
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, collectLams]
    change ((lowerStmt Φ s₂).run ((lowerStmt Φ s₁).run b).2).2.nextLam =
        ((collectLams s₂).run ((collectLams s₁).run b.nextLam).2).2 ∧
      ((lowerStmt Φ s₂).run ((lowerStmt Φ s₁).run b).2).2.callGadgets.map
          (fun site => (site.lamID, site.body)) =
        b.callGadgets.map (fun site => (site.lamID, site.body)) ++
          ((collectLams s₁).run b.nextLam).1 ++
          ((collectLams s₂).run ((collectLams s₁).run b.nextLam).2).1
    rcases h₁ : StateT.run (lowerStmt Φ s₁) b with ⟨r₁, b₁⟩
    rcases c₁ : StateT.run (collectLams s₁) b.nextLam with ⟨ls₁, n₁⟩
    have H₁ := ih₁ b
    rw [h₁, c₁] at H₁
    simp only at H₁
    rcases h₂ : StateT.run (lowerStmt Φ s₂) b₁ with ⟨r₂, b₂⟩
    rcases c₂ : StateT.run (collectLams s₂) n₁ with ⟨ls₂, n₂⟩
    have H₂ := ih₂ b₁
    rw [H₁.1, h₂, c₂] at H₂
    simp only at H₂
    have result : b₂.nextLam = n₂ ∧
        b₂.callGadgets.map (fun site => (site.lamID, site.body)) =
          b.callGadgets.map (fun site => (site.lamID, site.body)) ++ ls₁ ++ ls₂ :=
      ⟨H₂.1, by rw [H₂.2, H₁.2, List.append_assoc]⟩
    rw [h₁, h₂, c₁, c₂]
    exact result
  | If c t f iht ihf =>
    let b₀ : BState :=
      { cfg := { nodes := b.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1 + 1 + 1, nextLam := b.nextLam,
        callGadgets := b.callGadgets }
    simp only [lowerStmt, StateT.run_bind, StateT.run_pure, addNode_run, addEdge_run,
      collectLams]
    change ((lowerStmt Φ f).run ((lowerStmt Φ t).run b₀).2).2.nextLam =
        ((collectLams f).run ((collectLams t).run b.nextLam).2).2 ∧
      ((lowerStmt Φ f).run ((lowerStmt Φ t).run b₀).2).2.callGadgets.map
          (fun site => (site.lamID, site.body)) =
        b.callGadgets.map (fun site => (site.lamID, site.body)) ++
          ((collectLams t).run b.nextLam).1 ++
          ((collectLams f).run ((collectLams t).run b.nextLam).2).1
    rcases ht : StateT.run (lowerStmt Φ t) b₀ with ⟨rt, bt⟩
    rcases ct : StateT.run (collectLams t) b.nextLam with ⟨lt, nt⟩
    have Ht := iht b₀
    rw [ht, ct] at Ht
    simp only at Ht
    rcases hf : StateT.run (lowerStmt Φ f) bt with ⟨rf, bf⟩
    rcases cf : StateT.run (collectLams f) nt with ⟨lf, nf⟩
    have Hf := ihf bt
    rw [Ht.1, hf, cf] at Hf
    simp only at Hf
    have result : bf.nextLam = nf ∧
        bf.callGadgets.map (fun site => (site.lamID, site.body)) =
          b.callGadgets.map (fun site => (site.lamID, site.body)) ++ lt ++ lf :=
      ⟨Hf.1, by rw [Hf.2, Ht.2, List.append_assoc]⟩
    rw [ht, hf, ct, cf]
    exact result
  | While c body ih =>
    let b₀ : BState :=
      { cfg := { nodes := b.cfg.nodes ++ [.Skip] ++ [.Assume c] ++ [.Assume (.Not c)],
                 edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1 + 1 + 1, nextLam := b.nextLam,
        callGadgets := b.callGadgets }
    change ((lowerStmt Φ body).run b₀).2.nextLam =
        ((collectLams body).run b.nextLam).2 ∧
      ((lowerStmt Φ body).run b₀).2.callGadgets.map (fun site => (site.lamID, site.body)) =
        b.callGadgets.map (fun site => (site.lamID, site.body)) ++
          ((collectLams body).run b.nextLam).1
    rcases hb : StateT.run (lowerStmt Φ body) b₀ with ⟨rb, bb⟩
    have Hb := ih b₀
    rw [hb] at Hb
    simp only at Hb
    simpa [b₀] using Hb
  | Call f body ih =>
    let b₀ : BState :=
      { cfg := { nodes := b.cfg.nodes ++ [.Call f b.nextLam], edges := b.cfg.edges,
                 entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1, nextLam := b.nextLam + 1,
        callGadgets := b.callGadgets }
    change ((lowerStmt Φ body).run b₀).2.nextLam =
        ((collectLams body).run (b.nextLam + 1)).2 ∧
      (((lowerStmt Φ body).run b₀).2.callGadgets ++
        [⟨b.nextID, f, b.nextLam, callKind Φ f,
          ((lowerStmt Φ body).run b₀).1.1, ((lowerStmt Φ body).run b₀).1.2,
          ((lowerStmt Φ body).run b₀).2.nextID, body⟩]).map
          (fun site => (site.lamID, site.body)) =
        b.callGadgets.map (fun site => (site.lamID, site.body)) ++
          (b.nextLam, body) :: ((collectLams body).run (b.nextLam + 1)).1
    rcases hb : StateT.run (lowerStmt Φ body) b₀ with ⟨rb, bb⟩
    rcases cb : StateT.run (collectLams body) (b.nextLam + 1) with ⟨lb, nb⟩
    have Hb := ih b₀
    rw [hb, cb] at Hb
    simp only at Hb
    have result : bb.nextLam = nb ∧
        (bb.callGadgets ++
          [⟨b.nextID, f, b.nextLam, callKind Φ f, rb.1, rb.2, bb.nextID, body⟩]).map
            (fun site => (site.lamID, site.body)) =
          b.callGadgets.map (fun site => (site.lamID, site.body)) ++ (b.nextLam, body) :: lb := by
      constructor
      · exact Hb.1
      · rw [List.map_append, List.map_cons, Hb.2]
        simp [b₀, List.append_assoc]
    rw [hb, cb]
    exact result
  -/

/-- Every construction-time call-gadget certificate in a generated CFG is the
lambda occurrence allocated by the matching collector run. -/
theorem Stmt.generatedCFGFrom_callGadget_provenance
    (Φ : FunEnv) (startLam : Nat) (s : Stmt) {site : CallGadget}
    (hsite : site ∈ (s.generatedCFGFrom Φ startLam).callGadgets) :
    (site.lamID, site.body) ∈ ((collectLams s).run startLam).1 := by
  have h := lowerStmt_callGadgets_collectLams Φ s
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
  simp only [Stmt.generatedCFGFrom] at hsite
  simpa using (h.2 site hsite).resolve_left (by simp)

/-- A syntactic call occurrence, named by the same globally fresh lambda id
    that `lowerStmt` puts in its `NodeKind.Call` node.  Keeping the body here
    is important: it identifies the lambda CFG that `Program.family` must
    register, including for calls nested arbitrarily deeply in another lambda. -/
structure CallSite where
  lamID : Nat
  body : Stmt
deriving DecidableEq, Repr

/-- Enumerate all call occurrences in lowering order.  This deliberately uses
    `collectLams`, rather than a second traversal with a subtly different
    counter discipline, so its ids are exactly the ids consumed by lowering. -/
def Stmt.callSites (s : Stmt) : StateM Nat (List CallSite) := fun start =>
  let out := (collectLams s).run start
  (out.1.map fun pair => { lamID := pair.1, body := pair.2 }, out.2)

/-- The call-site trace and lambda collector share both order and allocation.
    This is the bridge from nested lowering provenance to family registration. -/
theorem Stmt.callSites_collectLams (s : Stmt) (start : Nat) :
    ((s.callSites.run start).1.map fun site => (site.lamID, site.body)) =
      ((collectLams s).run start).1 := by
  change List.map (fun site : CallSite => (site.lamID, site.body))
      (((collectLams s).run start).1.map fun pair =>
        { lamID := pair.1, body := pair.2 }) = ((collectLams s).run start).1
  induction ((collectLams s).run start).1 with
  | nil => rfl
  | cons pair rest ih => simp [ih]

-- # Family of CFGs

/-- lists of CFGs for functions & lambdas + single CFG for main -/
structure CFGFamily where
  funCFGs : List (String × InvKind × WFCFG)
  lamCFGs : List (Nat × WFCFG) := []
  mainCFG : WFCFG

private def familyStep (p : Program) := fun
    (acc : List (String × InvKind × WFCFG) × List (Nat × Stmt) × Nat)
    (fb : String × InvKind × Stmt) =>
  let (funs, lams, c) := acc
  let (f, κ, body) := fb
  let wrapped := Stmt.Seq body Stmt.Skip
  let (bl, c') := (collectLams wrapped).run c
  (funs ++ [(f, κ, wrapped.wfcfgFrom p.phi c)], lams ++ bl, c')

/-- Lower a `Program` into its family of well-formed CFGs: every `(f, κ, body)`
    binding in `Φ` becomes `(f, κ, (body ;; skip).wfcfg Φ)`, and `p.main`
    becomes `mainCFG`. -/
def Program.family (p : Program) : CFGFamily :=
  let (mainLams, c₁) := (collectLams p.main).run 0
  let (funCFGs, funLams, _) := p.phi.foldl (familyStep p) ([], [], c₁)
  { funCFGs := funCFGs
    mainCFG := p.main.wfcfg p.phi
    lamCFGs := (mainLams ++ funLams).map (fun (ℓ, body) =>
      (ℓ, (body ;; Stmt.Skip).wfcfgFrom p.phi (ℓ + 1))) }

/-- The certificate-bearing companion to `CFGFamily`. Every component retains
its generated graph and the proof that its call-site certificates account for
the component's summary edges. -/
structure GeneratedCFGFamily where
  funCFGs : List (String × InvKind × CertifiedGeneratedCFG)
  lamCFGs : List (Nat × CertifiedGeneratedCFG) := []
  mainCFG : CertifiedGeneratedCFG

def CertifiedGeneratedCFG.wfcfg (component : CertifiedGeneratedCFG) : WFCFG :=
  ⟨component.generated.cfg, component.wellFormed⟩

@[simp] theorem Stmt.certifiedGeneratedCFGFrom_wfcfg
    (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    (s.certifiedGeneratedCFGFrom Φ startLam).wfcfg = s.wfcfgFrom Φ startLam := rfl

@[simp] theorem Stmt.certifiedGeneratedCFG_wfcfg (Φ : FunEnv) (s : Stmt) :
    (s.certifiedGeneratedCFG Φ).wfcfg = s.wfcfg Φ := rfl

/-- Forget construction-time certificates, recovering the pre-existing family
shape for clients that only consume well-formed CFGs. -/
def GeneratedCFGFamily.erase (fam : GeneratedCFGFamily) : CFGFamily :=
  { funCFGs := fam.funCFGs.map fun (f, κ, component) => (f, κ, component.wfcfg)
    lamCFGs := fam.lamCFGs.map fun (ℓ, component) => (ℓ, component.wfcfg)
    mainCFG := fam.mainCFG.wfcfg }

private def generatedFamilyStep (p : Program) := fun
    (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat)
    (fb : String × InvKind × Stmt) =>
  let (funs, lams, c) := acc
  let (f, κ, body) := fb
  let wrapped := Stmt.Seq body Stmt.Skip
  let (bl, c') := (collectLams wrapped).run c
  (funs ++ [(f, κ, wrapped.certifiedGeneratedCFGFrom p.phi c)], lams ++ bl, c')

/-- Lower every program component to a certificate-bearing CFG. The allocation
and component order intentionally mirror `Program.family`, including the
lambda-id offsets used for functions and registered lambda bodies. -/
def Program.generatedFamily (p : Program) : GeneratedCFGFamily :=
  let (mainLams, c₁) := (collectLams p.main).run 0
  let (funCFGs, funLams, _) := p.phi.foldl (generatedFamilyStep p) ([], [], c₁)
  { funCFGs := funCFGs
    mainCFG := p.main.certifiedGeneratedCFG p.phi
    lamCFGs := (mainLams ++ funLams).map (fun (ℓ, body) =>
      (ℓ, (body ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (ℓ + 1))) }

/-
Every function component accumulated by `generatedFamilyStep` is the
canonical certified lowering of its recorded source, environment, and lambda
counter.
-/
private theorem generatedFamilyFold_components_canonical (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      (∀ entry ∈ acc.1,
        entry.2.2 = entry.2.2.source.certifiedGeneratedCFGFrom
          p.phi entry.2.2.startLam) →
      ∀ entry ∈ (xs.foldl (generatedFamilyStep p) acc).1,
        entry.2.2 = entry.2.2.source.certifiedGeneratedCFGFrom
          p.phi entry.2.2.startLam := by
  intro xs
  induction xs with
  | nil =>
      intro acc hacc entry hentry
      exact hacc entry hentry
  | cons hd tl ih =>
      intro acc hacc
      simp only [List.foldl]
      apply ih
      intro entry hentry
      unfold generatedFamilyStep at hentry
      generalize hrun :
        (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out at hentry
      rcases out with ⟨lams, next⟩
      simp only [hrun, List.mem_append, List.mem_singleton] at hentry
      rcases hentry with hold | hnew
      · exact hacc entry hold
      · rcases hnew with rfl
        rfl

/-- Collecting a call body recursively accounts for all calls nested in that
body.  This closure property lets a generated lambda component inherit the
registration of any call gadget it contains. -/
private theorem collectLams_nested_mem (s : Stmt) : ∀ {start ℓ body ℓ' body'},
    (ℓ, body) ∈ ((collectLams s).run start).1 →
    (ℓ', body') ∈ ((collectLams body).run (ℓ + 1)).1 →
    (ℓ', body') ∈ ((collectLams s).run start).1 := by
  intro start ℓ body ℓ' body' houter hinner
  induction s generalizing start ℓ body ℓ' body' <;>
    simp [collectLams, StateT.run_bind, StateT.run_pure, id_bind, id_map, id_pure] at *
  all_goals grind

private theorem find?_eq_some_of_mem_nodup
    (xs : List (Nat × CertifiedGeneratedCFG)) (ℓ : Nat) (component : CertifiedGeneratedCFG)
    (hnodup : (xs.map Prod.fst).Nodup) (hmem : (ℓ, component) ∈ xs) :
    xs.find? (·.1 = ℓ) = some (ℓ, component) := by
  induction xs with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨headℓ, headComponent⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.mem_cons] at hmem
    by_cases hhead : headℓ = ℓ
    · subst headℓ
      have hcomponent : headComponent = component := by
        rcases hmem with hmem | hmem
        · exact (Prod.mk.inj hmem).2.symm
        · exact False.elim (hnodup.1 (List.mem_map_of_mem hmem))
      subst headComponent
      simp
    · simp only [hhead, decide_false, Bool.false_eq_true, not_false_eq_true,
      List.find?_cons_of_neg]
      rcases hmem with hmem | hmem
      · exact False.elim (hhead (Prod.mk.inj hmem).1.symm)
      · exact ih hnodup.2 hmem

private theorem generatedFamilyFold_lam_ids (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      ∀ start, acc.2.1.map Prod.fst = List.range' start acc.2.1.length →
        acc.2.2 = start + acc.2.1.length →
      ((xs.foldl (generatedFamilyStep p) acc).2.1).map Prod.fst =
        List.range' start ((xs.foldl (generatedFamilyStep p) acc).2.1).length := by
  intro xs
  induction xs with
  | nil => intro acc start hacc _; exact hacc
  | cons hd tl ih =>
    intro acc start hacc hcounter
    simp only [List.foldl]
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    have halloc := collectLams_allocation (hd.2.2 ;; Stmt.Skip) acc.2.2
    rw [hrun] at halloc
    simp only at halloc
    apply ih
    · simp only [generatedFamilyStep, hrun, List.map_append]
      rw [hacc, halloc.2, hcounter]
      simp only [List.length_append]
      simpa using (List.range'_append (s := start) (m := acc.2.1.length)
      (n := bl.length) (step := 1))
    · simp only [generatedFamilyStep, hrun]
      simp only [List.length_append]
      rw [halloc.1, hcounter]
      change start + acc.2.1.length + bl.length = start + (acc.2.1.length + bl.length)
      omega

/-- Function-family collection allocates consecutive lambda identifiers from
the counter inherited from the main component. -/
private theorem generatedFamilyFold_new_lam_ids (p : Program) :
    ∀ (xs : FunEnv) (start : Nat),
      ((xs.foldl (generatedFamilyStep p) ([], [], start)).2.1).map Prod.fst =
        List.range' start ((xs.foldl (generatedFamilyStep p) ([], [], start)).2.1).length := by
  intro xs start
  apply generatedFamilyFold_lam_ids p xs ([], [], start) start
  · rfl
  · rfl

private theorem generatedFamilyFold_gadget_mem (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      (∀ f κ source, (f, κ, source) ∈ acc.1 → ∀ site ∈ source.generated.callGadgets,
        (site.lamID, site.body) ∈ acc.2.1) →
      ∀ f κ source, (f, κ, source) ∈ (xs.foldl (generatedFamilyStep p) acc).1 →
        ∀ site ∈ source.generated.callGadgets,
          (site.lamID, site.body) ∈ (xs.foldl (generatedFamilyStep p) acc).2.1 := by
  intro xs
  induction xs with
  | nil =>
    intro acc hacc f κ source hsource site hsite
    exact hacc f κ source hsource site hsite
  | cons hd tl ih =>
    intro acc hacc f κ source hsource site hsite
    simp only [List.foldl] at hsource ⊢
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    apply ih
    · intro f κ source hsource site hsite
      simp only [generatedFamilyStep, hrun, List.mem_append, List.mem_cons] at hsource ⊢
      rcases hsource with hsource | hsource
      · exact Or.inl (hacc f κ source hsource site hsite)
      · rcases hsource with hsource | hsource
        · rcases hsource with ⟨rfl, rfl, rfl⟩
          exact Or.inr (by
            simpa [hrun] using
              (Stmt.generatedCFGFrom_callGadget_provenance p.phi acc.2.2
                (hd.2.2 ;; Stmt.Skip) hsite))
        · simp at hsource
    · exact hsource
    · exact hsite

private theorem generatedFamilyFold_lam_nested_mem (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      (∀ ℓ body, (ℓ, body) ∈ acc.2.1 → ∀ ℓ' body',
        (ℓ', body') ∈ ((collectLams body).run (ℓ + 1)).1 → (ℓ', body') ∈ acc.2.1) →
      ∀ ℓ body, (ℓ, body) ∈ (xs.foldl (generatedFamilyStep p) acc).2.1 → ∀ ℓ' body',
        (ℓ', body') ∈ ((collectLams body).run (ℓ + 1)).1 →
          (ℓ', body') ∈ (xs.foldl (generatedFamilyStep p) acc).2.1 := by
  intro xs
  induction xs with
  | nil =>
    intro acc hacc ℓ body houter ℓ' body' hinner
    exact hacc ℓ body houter ℓ' body' hinner
  | cons hd tl ih =>
    intro acc hacc ℓ body houter ℓ' body' hinner
    simp only [List.foldl] at houter ⊢
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    apply ih
    · intro ℓ body houter ℓ' body' hinner
      simp only [generatedFamilyStep, hrun, List.mem_append] at houter ⊢
      rcases houter with houter | houter
      · exact Or.inl (hacc ℓ body houter ℓ' body' hinner)
      · exact Or.inr (by
          have houter' : (ℓ, body) ∈
              ((collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2).1 := by
            simpa only [hrun] using houter
          simpa [hrun] using
            (collectLams_nested_mem (hd.2.2 ;; Stmt.Skip) (start := acc.2.2)
              houter' hinner))
    · exact houter
    · exact hinner

namespace GeneratedCFGFamily

/-- Resolve a certificate-bearing component using the same reference scheme as
the ordinary `CFGFamily` resolver. -/
def cfgAt? (fam : GeneratedCFGFamily) : CFGRef → Option CertifiedGeneratedCFG
| .main  => some fam.mainCFG
| .fn f  => (fam.funCFGs.find? (·.1 = f)).map (·.2.2)
| .lam ℓ => (fam.lamCFGs.find? (·.1 = ℓ)).map (·.2)

@[simp] theorem cfgAt_main (fam : GeneratedCFGFamily) :
    fam.cfgAt? .main = some fam.mainCFG := rfl

/-
A component resolved from a generated program family is exactly the
canonical certified lowering recorded by its `source` and `startLam` fields.
-/
theorem Program.generatedFamily_component_canonical (p : Program) {ref : CFGRef}
    {component : CertifiedGeneratedCFG}
    (hresolve : p.generatedFamily.cfgAt? ref = some component) :
    component = component.source.certifiedGeneratedCFGFrom p.phi component.startLam := by
  cases ref;
  · cases hresolve;
    rfl;
  · contrapose! hresolve; simp_all +decide only [ne_eq, cfgAt?, Option.map_eq_some_iff,
    Prod.exists, exists_eq_right, not_exists] ;
    intro f κ hfind
    have := List.mem_of_find?_eq_some hfind
    simp_all +decide only [Program.generatedFamily, List.map_append]
    exact hresolve <| by simpa using
      generatedFamilyFold_components_canonical p p.phi ([], [], (collectLams p.main).run 0 |>.2) (by simp) _ this;
  · simp +decide [ GeneratedCFGFamily.cfgAt? ] at hresolve;
    grind +locals

/-- A resolved component exposes the complete κ-gadget for every recorded
certificate. -/
theorem cfgAt_gadget_present (fam : GeneratedCFGFamily) {ref : CFGRef}
    {component : CertifiedGeneratedCFG} (_hresolve : fam.cfgAt? ref = some component)
    {site : CallGadget} (hsite : site ∈ component.generated.callGadgets) :
    component.generated.cfg.HasKappaGadget
      site.kappa site.en site.enL site.exL site.ret :=
  component.gadget_present hsite

/-- Every summary edge in a resolved generated component has a retained
construction-time gadget witness. -/
theorem cfgAt_summary_has_gadget (fam : GeneratedCFGFamily) {ref : CFGRef}
    {component : CertifiedGeneratedCFG} (_hresolve : fam.cfgAt? ref = some component)
    {e : Edge} (he : e ∈ component.generated.cfg.edges) (hk : e.kind = .summary) :
    ∃ site ∈ component.generated.callGadgets, e ∈ site.edges :=
  component.summary_has_gadget he hk

/-- A resolved component's summary edges originate at call nodes, and their
retained gadget certificates identify the corresponding summary edge. -/
theorem cfgAt_summary_has_gadget_and_call_node (fam : GeneratedCFGFamily)
    {ref : CFGRef} {component : CertifiedGeneratedCFG}
    (_hresolve : fam.cfgAt? ref = some component)
    {e : Edge} (he : e ∈ component.generated.cfg.edges) (hk : e.kind = .summary) :
    (∃ site ∈ component.generated.callGadgets, e ∈ site.edges) ∧
      ∃ f ℓ, component.generated.cfg.nodeKind e.src = some (.Call f ℓ) :=
  ⟨component.summary_has_gadget he hk,
    component.wellFormed.2.2.2.2.1 e he hk⟩

/-- Summary targets are unique for a certificate witnessed in a resolved
component, independently of any properties of unrelated well-formed CFGs. -/
theorem cfgAt_summary_target_unique (fam : GeneratedCFGFamily) {ref : CFGRef}
    {component : CertifiedGeneratedCFG} (_hresolve : fam.cfgAt? ref = some component)
    {site : CallGadget} (hsite : site ∈ component.generated.callGadgets)
    {e₁ e₂ : Edge} (he₁ : e₁ ∈ site.edges) (hk₁ : e₁.kind = .summary)
    (he₂ : e₂ ∈ site.edges) (hk₂ : e₂.kind = .summary) : e₁.dst = e₂.dst :=
  component.summary_target_unique hsite he₁ hk₁ he₂ hk₂

end GeneratedCFGFamily

/-- Certificate-bearing lowering output for the program's main component.
This is the provenance interface paired with `p.family.mainCFG`; the latter
remains unchanged for existing CFG-family consumers. -/
def Program.generatedMainCFG (p : Program) : GeneratedCFG :=
  p.main.generatedCFG p.phi

namespace CFGFamily

/-- Resolve a CFG reference through the family, if it is registered. -/
def cfgAt? (fam : CFGFamily) : CFGRef → Option WFCFG
| .main  => some fam.mainCFG
| .fn f  => (fam.funCFGs.find? (·.1 = f)).map (·.2.2)
| .lam ℓ => (fam.lamCFGs.find? (·.1 = ℓ)).map (·.2)

/-- The distinguished main CFG is always resolvable through a family. -/
@[simp] theorem cfgAt_main (fam : CFGFamily) :
    fam.cfgAt? .main = some fam.mainCFG := rfl

/-- A function entry in a family makes the corresponding function reference resolvable. -/
theorem fn_registered_of_mem (fam : CFGFamily) {f : String} {κ : InvKind} {cfg : WFCFG}
    (hmem : (f, κ, cfg) ∈ fam.funCFGs) :
    ∃ cfg, fam.cfgAt? (.fn f) = some cfg := by
  let found := fam.funCFGs.find? (·.1 = f)
  have hfound : found ≠ none := by
    intro hnone
    have hnone' : fam.funCFGs.find? (·.1 = f) = none := by
      simpa [found] using hnone
    rw [List.find?_eq_none] at hnone'
    exact hnone' _ hmem (by simp)
  rcases hopt : found with _ | entry
  · exact False.elim (hfound hopt)
  · exact ⟨entry.2.2, by simp [cfgAt?, found, hopt]⟩

/-- A lambda entry in a family makes the corresponding lambda reference resolvable. -/
theorem lam_registered_of_mem (fam : CFGFamily) {ℓ : Nat} {cfg : WFCFG}
    (hmem : (ℓ, cfg) ∈ fam.lamCFGs) :
    ∃ cfg, fam.cfgAt? (.lam ℓ) = some cfg := by
  let found := fam.lamCFGs.find? (·.1 = ℓ)
  have hfound : found ≠ none := by
    intro hnone
    have hnone' : fam.lamCFGs.find? (·.1 = ℓ) = none := by
      simpa [found] using hnone
    rw [List.find?_eq_none] at hnone'
    exact hnone' _ hmem (by simp)
  rcases hopt : found with _ | entry
  · exact False.elim (hfound hopt)
  · exact ⟨entry.2, by simp [cfgAt?, found, hopt]⟩

end CFGFamily

private theorem find?_erase_funCFGs
    (xs : List (String × InvKind × CertifiedGeneratedCFG)) (f : String) :
    (xs.map fun (name, κ, component) => (name, κ, component.wfcfg)).find? (·.1 = f) =
      (xs.find? (·.1 = f)).map fun (name, κ, component) => (name, κ, component.wfcfg) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.find?_cons]
    split <;> simp [*]

private theorem find?_erase_lamCFGs
    (xs : List (Nat × CertifiedGeneratedCFG)) (ℓ : Nat) :
    (xs.map fun (lamID, component) => (lamID, component.wfcfg)).find? (·.1 = ℓ) =
      (xs.find? (·.1 = ℓ)).map fun (lamID, component) => (lamID, component.wfcfg) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.find?_cons]
    split <;> simp [*]

/-- Resolving a certificate-erased family is equivalent to resolving its
certificate-bearing source and then forgetting the certificate. -/
theorem GeneratedCFGFamily.erase_cfgAt? (fam : GeneratedCFGFamily) (ref : CFGRef) :
    fam.erase.cfgAt? ref = (fam.cfgAt? ref).map CertifiedGeneratedCFG.wfcfg := by
  cases ref with
  | main => rfl
  | fn f =>
    change
      ((fam.funCFGs.map fun (name, κ, component) =>
          (name, κ, component.wfcfg)).find? (·.1 = f)).map (·.2.2) =
        ((fam.funCFGs.find? (·.1 = f)).map (·.2.2)).map CertifiedGeneratedCFG.wfcfg
    rw [find?_erase_funCFGs]
    simp only [Option.map_map, Function.comp_def]
  | lam ℓ =>
    change
      ((fam.lamCFGs.map fun (lamID, component) =>
          (lamID, component.wfcfg)).find? (·.1 = ℓ)).map (·.2) =
        ((fam.lamCFGs.find? (·.1 = ℓ)).map (·.2)).map CertifiedGeneratedCFG.wfcfg
    rw [find?_erase_lamCFGs]
    simp only [Option.map_map, Function.comp_def]

private def eraseFamilyAcc
    (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat) :
    List (String × InvKind × WFCFG) × List (Nat × Stmt) × Nat :=
  (acc.1.map fun (f, κ, component) => (f, κ, component.wfcfg), acc.2)

private theorem generatedFamilyFold_erase (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      eraseFamilyAcc (xs.foldl (generatedFamilyStep p) acc) =
        xs.foldl (familyStep p) (eraseFamilyAcc acc) := by
  intro xs
  induction xs with
  | nil => intro acc; rfl
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl]
    rw [ih]
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    simp [hrun, generatedFamilyStep, familyStep, eraseFamilyAcc]

/-- Forgetting construction-time certificates from a generated family recovers
exactly the existing program CFG family. -/
theorem Program.generatedFamily_erase (p : Program) :
    p.generatedFamily.erase = p.family := by
  unfold Program.generatedFamily Program.family GeneratedCFGFamily.erase
  generalize hmain : (collectLams p.main).run 0 = mainResult
  rcases mainResult with ⟨mainLams, c₁⟩
  simp only
  generalize hgen : p.phi.foldl (generatedFamilyStep p) ([], [], c₁) = generatedResult
  rcases generatedResult with ⟨funCFGs, funLams, c⟩
  have hfold := generatedFamilyFold_erase p p.phi ([], [], c₁)
  rw [hgen] at hfold
  simp only [eraseFamilyAcc, List.map_nil] at hfold
  rw [← hfold]
  have hlam :
      (fun x : Nat × CertifiedGeneratedCFG => (x.1, x.2.wfcfg)) ∘
          (fun x : Nat × Stmt =>
            (x.1, (x.2 ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (x.1 + 1))) =
        (fun x : Nat × Stmt =>
          (x.1, (x.2 ;; Stmt.Skip).wfcfgFrom p.phi (x.1 + 1))) := by
    funext x
    rcases x with ⟨ℓ, body⟩
    simp
  simp only [List.map_map, hlam, Stmt.certifiedGeneratedCFG_wfcfg]

/-- Existing family-resolution hypotheses can be lifted to the corresponding
certificate-bearing generated component. -/
theorem Program.family_cfgAt?_iff_generatedFamily (p : Program) (ref : CFGRef) (cfg : WFCFG) :
    p.family.cfgAt? ref = some cfg ↔
      ∃ component, p.generatedFamily.cfgAt? ref = some component ∧ component.wfcfg = cfg := by
  rw [← p.generatedFamily_erase, GeneratedCFGFamily.erase_cfgAt?]
  constructor
  · intro h
    cases hresolve : p.generatedFamily.cfgAt? ref with
    | none => simp [hresolve] at h
    | some component =>
      refine ⟨component, rfl, ?_⟩
      simpa [hresolve] using h
  · rintro ⟨component, hresolve, hcomponent⟩
    simp [hresolve, hcomponent]

/-- Every call gadget of a resolved generated component has its standalone
lambda component registered at exactly the identifier assigned during lowering.
This includes gadgets in the main component, function components, and lambda
components nested at arbitrary depth. -/
theorem Program.generatedFamily_gadget_standalone (p : Program) {ref : CFGRef}
    {source : CertifiedGeneratedCFG}
    (hresolve : p.generatedFamily.cfgAt? ref = some source)
    {site : CallGadget} (hsite : site ∈ source.generated.callGadgets) :
    p.generatedFamily.cfgAt? (.lam site.lamID) =
      some ((site.body ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (site.lamID + 1)) := by
  unfold Program.generatedFamily at hresolve ⊢
  generalize hmain : (collectLams p.main).run 0 = mainResult
  rcases mainResult with ⟨mainLams, c₁⟩
  generalize hfold : p.phi.foldl (generatedFamilyStep p) ([], [], c₁) = foldResult
  rcases foldResult with ⟨funCFGs, funLams, c₂⟩
  have hmainAlloc := collectLams_allocation p.main 0
  rw [hmain] at hmainAlloc
  simp only at hmainAlloc
  have hfunIds := generatedFamilyFold_new_lam_ids p p.phi c₁
  rw [hfold] at hfunIds
  simp only at hfunIds
  have hnodup : ((mainLams ++ funLams).map Prod.fst).Nodup := by
    rw [List.map_append, hmainAlloc.2, hfunIds, hmainAlloc.1]
    have happend : List.range' 0 mainLams.length ++
        List.range' (0 + mainLams.length) funLams.length =
        List.range' 0 (mainLams.length + funLams.length) := by
      simpa using (List.range'_append (s := 0) (m := mainLams.length)
        (n := funLams.length) (step := 1))
    rw [happend]
    exact List.nodup_range' 1
  have hmainNested : ∀ ℓ body, (ℓ, body) ∈ mainLams → ∀ ℓ' body',
      (ℓ', body') ∈ ((collectLams body).run (ℓ + 1)).1 → (ℓ', body') ∈ mainLams := by
    intro ℓ body houter ℓ' body' hinner
    have houter' : (ℓ, body) ∈ ((collectLams p.main).run 0).1 := by
      rw [hmain]
      exact houter
    have h := collectLams_nested_mem p.main houter' hinner
    simpa only [hmain] using h
  have hfunNested := generatedFamilyFold_lam_nested_mem p p.phi ([], [], c₁) (by simp)
  rw [hfold] at hfunNested
  simp only at hfunNested
  have hfunGadgets := generatedFamilyFold_gadget_mem p p.phi ([], [], c₁) (by simp)
  rw [hfold] at hfunGadgets
  simp only at hfunGadgets
  rw [hmain] at hresolve
  simp only at hresolve
  rw [hfold] at hresolve
  simp only at hresolve
  simp only
  rw [hfold]
  simp only
  have hpair : (site.lamID, site.body) ∈ mainLams ++ funLams := by
    cases ref with
    | main =>
      change some (p.main.certifiedGeneratedCFG p.phi) = some source at hresolve
      simp only [Option.some.injEq] at hresolve
      subst source
      apply List.mem_append_left
      simpa [hmain] using Stmt.generatedCFGFrom_callGadget_provenance p.phi 0 p.main hsite
    | fn f =>
      change (funCFGs.find? (fun x => x.1 = f)).map (·.2.2) = some source at hresolve
      cases hfound : funCFGs.find? (fun x => x.1 = f) with
      | none => simp [hfound] at hresolve
      | some entry =>
        rcases entry with ⟨name, κ, component⟩
        simp only [hfound, Option.map_some, Option.some.injEq] at hresolve
        subst source
        apply List.mem_append_right
        apply hfunGadgets name κ component
        · exact List.mem_of_find?_eq_some hfound
        · exact hsite
    | lam ℓ =>
      let entries := (mainLams ++ funLams).map
        (fun x => (x.1, (x.2 ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (x.1 + 1)))
      change (entries.find? (fun x => x.1 = ℓ)).map Prod.snd = some source at hresolve
      cases hfound : entries.find? (fun x => x.1 = ℓ) with
      | none => simp [hfound] at hresolve
      | some entry =>
        rcases entry with ⟨lamID, component⟩
        simp only [hfound, Option.map_some, Option.some.injEq] at hresolve
        subst source
        have hentry := List.mem_of_find?_eq_some hfound
        dsimp [entries] at hentry
        simp only [List.mem_map] at hentry
        rcases hentry with ⟨outer, houter, houterEq⟩
        rcases outer with ⟨outerID, outerBody⟩
        simp only [Prod.mk.injEq] at houterEq
        rcases houterEq with ⟨hID, hcomponent⟩
        subst lamID
        subst component
        have hinner : (site.lamID, site.body) ∈
            ((collectLams outerBody).run (outerID + 1)).1 := by
          simpa [collectLams, StateT.run_bind, StateT.run_pure, id_bind, id_map, id_pure] using
            (Stmt.generatedCFGFrom_callGadget_provenance p.phi (outerID + 1)
              (outerBody ;; Stmt.Skip) hsite)
        rcases List.mem_append.mp houter with houter | houter
        · exact List.mem_append_left _ (hmainNested outerID outerBody houter _ _ hinner)
        · exact List.mem_append_right _ (hfunNested outerID outerBody houter _ _ hinner)
  change (((mainLams ++ funLams).map fun x =>
    (x.1, (x.2 ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (x.1 + 1))).find?
      (fun x => x.1 = site.lamID)).map Prod.snd = _
  rw [find?_eq_some_of_mem_nodup
    (xs := (mainLams ++ funLams).map fun x =>
      (x.1, (x.2 ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (x.1 + 1)))
    (ℓ := site.lamID)
    (component := (site.body ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (site.lamID + 1))]
  · rfl
  · simpa only [List.map_map, Function.comp_apply] using hnodup
  · exact List.mem_map.mpr ⟨(site.lamID, site.body), hpair, rfl⟩

private theorem familyFold_preserves (p : Program) :
    ∀ (xs : FunEnv) (acc : List (String × InvKind × WFCFG) × List (Nat × Stmt) × Nat)
      (entry : String × InvKind × WFCFG),
      entry ∈ acc.1 → entry ∈ (xs.foldl (familyStep p) acc).1 := by
  intro xs
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    intro acc entry h
    simp only [List.foldl]
    refine ih _ entry ?_
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    simp [familyStep, hrun, h]

private theorem familyFold_registers (p : Program) :
    ∀ (xs : FunEnv) (acc : List (String × InvKind × WFCFG) × List (Nat × Stmt) × Nat)
      (f : String) (κ : InvKind) (body : Stmt),
      (f, κ, body) ∈ xs →
      ∃ cfg : WFCFG, (f, κ, cfg) ∈ (xs.foldl (familyStep p) acc).1 := by
  intro xs
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    intro acc f κ body h
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst hd
      refine ⟨(body ;; .Skip).wfcfgFrom p.phi acc.2.2, ?_⟩
      simp only [List.foldl]
      apply familyFold_preserves p tl _
      generalize hrun : (collectLams (body ;; Stmt.Skip)).run acc.2.2 = out
      rcases out with ⟨bl, c'⟩
      simp [familyStep, hrun]
    · simp only [List.foldl]
      exact ih _ _ _ _ h

private theorem lookup_mem (xs : FunEnv) (f : String) (κ : InvKind) (body : Stmt)
    (h : xs.lookup f = some (κ, body)) : (f, κ, body) ∈ xs := by
  induction xs generalizing f with
  | nil => simp [FunEnv.lookup] at h
  | cons hd tl ih =>
    simp only [FunEnv.lookup] at h
    split at h
    · rcases hd with ⟨g, κ', body'⟩
      simp only [Option.some.injEq] at h
      rcases h with ⟨hκ, hbody⟩
      subst f
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih f h)

/-- A successful environment lookup has a matching function CFG entry in `p.family`. -/
theorem Program.family_fun_binding (p : Program) {f : String} {κ : InvKind} {body : Stmt}
    (hlookup : p.phi.lookup f = some (κ, body)) :
    ∃ cfg : WFCFG, (f, κ, cfg) ∈ p.family.funCFGs := by
  unfold Program.family
  dsimp
  apply familyFold_registers p
  exact lookup_mem _ _ _ _ hlookup

/-- A successful environment lookup is resolvable through the CFG family. -/
theorem Program.family_fn_registered (p : Program) {f : String} {κ : InvKind} {body : Stmt}
    (hlookup : p.phi.lookup f = some (κ, body)) :
    ∃ cfg, p.family.cfgAt? (.fn f) = some cfg := by
  obtain ⟨cfg, hmem⟩ := p.family_fun_binding hlookup
  exact CFGFamily.fn_registered_of_mem p.family hmem

/-- The main component of `p.family` is available at the main reference. -/
@[simp] theorem Program.family_main_registered (p : Program) :
    p.family.cfgAt? .main = some p.family.mainCFG :=
  CFGFamily.cfgAt_main p.family

/-- Every lambda CFG entry of `p.family` is resolvable at its lambda reference.
    This membership form covers lambdas collected from both the main statement
    and function bodies. -/
theorem Program.family_lam_registered (p : Program) {ℓ : Nat} {cfg : WFCFG}
    (hmem : (ℓ, cfg) ∈ p.family.lamCFGs) :
    ∃ cfg', p.family.cfgAt? (.lam ℓ) = some cfg' :=
  CFGFamily.lam_registered_of_mem p.family hmem

/-- A lambda collected from the main statement is registered in `p.family`. -/
theorem Program.family_main_lam_registered (p : Program) {ℓ : Nat} {body : Stmt}
    (hcollect : (ℓ, body) ∈ ((collectLams p.main).run 0).1) :
    ∃ cfg, p.family.cfgAt? (.lam ℓ) = some cfg := by
  apply CFGFamily.lam_registered_of_mem
    (cfg := (body ;; Stmt.Skip).wfcfgFrom p.phi (ℓ + 1))
  unfold Program.family
  dsimp
  simp only [List.map_append]
  apply List.mem_append_left _
  exact List.mem_map.mpr ⟨(ℓ, body), hcollect, rfl⟩

/-- Every call occurrence in the main lowering trace resolves to its lambda
    component in `Program.family`.  Since `Stmt.callSites` is recursive through
    call bodies, this covers nested calls at every depth, not just root calls. -/
theorem Program.family_main_callSite_registered (p : Program) {site : CallSite}
    (hsite : site ∈ (p.main.callSites.run 0).1) :
    ∃ cfg, p.family.cfgAt? (.lam site.lamID) = some cfg := by
  apply p.family_main_lam_registered (body := site.body)
  have htrace := p.main.callSites_collectLams 0
  rw [← htrace]
  exact List.mem_map.mpr ⟨site, hsite, rfl⟩

-- # Graphviz (DOT) rendering

/-- Infix symbol for a binary operator, used in node labels. -/
def BinOp.symbol : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .lt  => "<"
  | .eq  => "=="
  | .and => "&&"

/-- Render an expression to a short human-readable string for CFG labels. -/
def FExpr.render : FExpr → String
  | .Null          => "null"
  | .Int n         => toString n
  | .Var x         => x
  | .IsNull e      => "isNull(" ++ e.render ++ ")"
  | .Not e         => "!" ++ e.render
  | .BinOp o e₁ e₂ => "(" ++ e₁.render ++ " " ++ BinOp.symbol o ++ " " ++ e₂.render ++ ")"

/-- A short label describing a CFG node. -/
def NodeKind.label : NodeKind → String
  | .Assume e   => "assume " ++ e.render
  | .Assign x e => x ++ " = " ++ e.render
  | .Skip       => "skip"
  | .Call f _   => "call " ++ f
  | .Invoke     => "invoke"

/-- Escape a string for inclusion inside a DOT double-quoted label. -/
def dotEscape (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\"" "\\\""

/-- One-character rendering of an invocation kind `κ` (ε/1/+/?). -/
def InvKind.symbol : InvKind → String
  | .none    => "ε"
  | .once    => "1"
  | .atLeast => "+"
  | .atMost  => "?"

def CFG.toDotStmts (g : CFG) (pfx : String) (ind : String) : String :=
  let nodeLines := g.nodes.mapIdx (fun i k =>
    let shape :=
      if i = g.entry && i = g.exit then ", shape=box, style=\"rounded,bold\""
      else if i = g.entry then ", shape=box, style=bold"
      else if i = g.exit then ", shape=doublecircle"
      else ""
    s!"{ind}{pfx}{i} [label=\"{i}: {dotEscape k.label}\"{shape}];")
  let edgeLines := g.edges.map (fun e =>
    let style := match e.kind with
      | .plain   => ""
      | .summary => " [style=dashed]"
    s!"{ind}{pfx}{e.src} -> {pfx}{e.dst}{style};")
  String.intercalate "\n" (nodeLines ++ edgeLines)

/-- Render a single CFG as a complete Graphviz `digraph`. -/
def CFG.toDot (g : CFG) (name : String := "cfg") : String :=
  "digraph \"" ++ dotEscape name ++ "\" {\n  node [shape=box];\n" ++
    g.toDotStmts "n" "  " ++ "\n}\n"

/-- Render an entire family of CFGs as one Graphviz `digraph`, placing each
    function CFG `G_f` and the top-level CFG in its own `subgraph cluster_*`.
    Node names are prefixed per cluster so per-CFG node IDs don't collide. -/
def CFGFamily.toDot (fam : CFGFamily) (name : String := "family") : String :=
  let lamClusters := fam.lamCFGs.mapIdx (fun i entry =>
    let (f, g) := entry
    "subgraph cluster_l" ++ toString i ++ " {\n" ++
      "    label=\"G_" ++ toString f ++ "\";\n" ++
      g.val.toDotStmts s!"l{i}_" "      " ++ "\n }")
  let funClusters := fam.funCFGs.mapIdx (fun i entry =>
    let (f, κ, g) := entry
    "  subgraph cluster_f" ++ toString i ++ " {\n" ++
      "    label=\"G_" ++ f ++ " (κ=" ++ κ.symbol ++ ")\";\n" ++
      g.val.toDotStmts s!"f{i}_" "    " ++ "\n  }")
  let mainCluster :=
    "  subgraph cluster_main {\n    label=\"main\";\n" ++
      fam.mainCFG.val.toDotStmts "main_" "    " ++ "\n  }"
  "digraph \"" ++ dotEscape name ++ "\" {\n  node [shape=box];\n" ++
    String.intercalate "\n" (funClusters ++ lamClusters ++ [mainCluster]) ++ "\n}\n"

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
  DukeAnalysisCFG g g.2

/-- All variables appearing in the program , de-duplicated, with a `Nodup` witness. -/
def vars (g : CFG) : { l : List String // l.Nodup } :=
  let base := g.nodes.filterMap (fun k =>
  match k with
  | .Assign x _ => some x
  | _           => none)
  ⟨base.eraseDups, Utils.List.eraseDups_nodup base⟩

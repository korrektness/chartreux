import Flow.Analysis.Generic
import Flow.Analysis.Worklist
import Flow.Analysis.WorklistProofs
import Flow.Duke.Eval
import Flow.Duke.CFG
import Flow.Duke.Utils
import Mathlib.Data.List.Nodup

namespace Duke.Analysis.Initialization

abbrev Loc := String

open Flow.Analysis
open Flow.Analysis.Generic

/-! ## Lattice definition -/

/-- For each location, is it uninitialized?
    (false - initialized, true - uninitialized)
-/
abbrev Fact (locs : List Loc) : Type := Domain locs.length Bool

def formatFact (locs : List Loc) (ℓ : Fact locs) : String :=
  let parts : List String :=
    (List.finRange locs.length).filterMap fun i =>
      let isUninitialized := ℓ i
      if isUninitialized then some (locs.get i) else none
  "uninit[" ++ String.intercalate ", " parts ++ "]"

/-! ## CFG transition functions -/

def evalExpr (locs : List Loc) (ℓ : Fact locs) : Expr → Bool
  | .Null => false
  | .Int _ => false
  | .Var x =>
      match locs.finIdxOf? x with
      | none   => true
      | some i => ℓ i
  | .IsNull e => evalExpr locs ℓ e
  | .Not e => evalExpr locs ℓ e
  | .BinOp _ e₁ e₂ => evalExpr locs ℓ e₁ ⊔ evalExpr locs ℓ e₂

def nodeTransfer (locs : List Loc) (g : CFG) (n : NodeID) :
    Fact locs -> Fact locs := fun ℓ =>
  match g.nodeKind n with
  | some (.Assign x _) =>
    match locs.finIdxOf? x with
    | none   => ℓ
    | some i => fun j => if j = i then false else ℓ j
  | some (.Assume _) | some .Skip | none => ℓ

def edgeTransfer (vars : List String) : Edge -> Fact vars -> Fact vars :=
  fun _ a => a

/-- The default initial fact: every tracked variable is uninitialized. -/
def entryInit (locs : List Loc) : Fact locs := fun _ => true

/-! ### Transfer function monotonicity -/

variable (cfg : WFCFG)
variable {locs : List Loc}

private lemma nodeTransfer_mono (n : NodeID) :
    mono_f (nodeTransfer locs cfg n) := by
  intro ℓ₁ ℓ₂ hxy
  funext j
  change (nodeTransfer locs cfg n ℓ₁) j ⊑ (nodeTransfer locs cfg n ℓ₂) j
  simp only
  unfold nodeTransfer
  generalize hk : cfg.val.nodeKind n = nk
  cases nk with
  | none => grind [Domain.ord_distr hxy]
  | some k =>
    cases k with (simp only; try grind [Domain.ord_distr hxy])
    | Assign x e =>
      generalize hx : locs.finIdxOf? x = a
      cases a <;> simp only <;> try split
      · apply Domain.ord_distr
        assumption
      · simp [max]
      · apply Domain.ord_distr
        assumption

private lemma edgeTransfer_mono :
    ∀ e, mono_f (edgeTransfer locs e) := fun _ _ _ h => h

instance instTransferMonoN :
    TransferMono (nodeTransfer locs cfg) (edgeTransfer locs) where
  node_mono := nodeTransfer_mono cfg
  edge_mono := edgeTransfer_mono

/-! ## Coherence predicate for concrete and abstract states -/

/-- For each variable, if the analysis tells us it is initialized, the concrete value exists -/
def coh (ℓ : Fact locs) (σ : State) : Prop :=
  ∀ i,
    ℓ i = false ->
    (σ (locs.get i)).isSome

/-- The DFA closure for initialization, parameterised by the underlying CFG.
    The CFG is needed to read `nodeKind`. -/
@[reducible]
def nDFA (locs : List Loc) : DFA NodeID Edge where
  L            := Fact locs
  nodeTransfer := nodeTransfer locs cfg
  edgeTransfer := edgeTransfer locs
  entry        := entryInit locs


private lemma preserve_update_none (ℓ : Fact locs)
    (hnone : locs.finIdxOf? x = none) (hcoh : coh ℓ σ) :
    coh ℓ (σ.updated x v) := by
  simp only [coh, State.updated] at *
  grind [List.finIdxOf?_eq_none_iff]

@[simp] private lemma DFA_transferAlong (cfg : WFCFG)
    (e : EdgeOf cfg.analysis) (ℓ : Fact locs) :
    (nDFA cfg locs).transferAlong cfg.analysis e ℓ =
    nodeTransfer locs cfg e.val.src ℓ := rfl

/-- The `DFASemantics` for a fixed CFG. The three preservation
    fields directly consume the abstract `LangSem` transitions. -/
def semantics (hnd : locs.Nodup) :
    DFASemantics (ls := dukeLangSem cfg) cfg.analysis (nDFA cfg locs) :=
  { Coh := coh
    isInit := State.isInit
    preserve_entry := by
      intro σ hinit
      cases hinit
      simp [coh, State.empty, entryInit]
    preserve_step := by
      intro e σ σ' ℓ hstep hcoh
      simp only [DFA_transferAlong, nodeTransfer]
      cases hstep with simp only [*]
      | @assign _ _ x expr v _ _ heval =>
        split
        · apply preserve_update_none <;> trivial
        · rename_i i hi
          intro j habs
          simp only at habs
          split_ifs at habs
          · subst j
            have hget := List.finIdxOf?_eq_some_iff.mp hi |>.left
            rw [Fin.getElem_fin] at hget
            rw [List.get_eq_getElem, hget, State.updated_eq σ x v]
            rfl
          · have h_x_neq : x ≠ locs.get j := by apply List.finIdxOf?_nodup <;> trivial
            rw [State.updated_neq] <;> try trivial
            apply hcoh; assumption
    preserve_stutter := by
      intro _n σ σ' ℓ hstut hcoh
      simp only [LangSem.LStutter] at hstut
      subst hstut
      assumption
  }

theorem mono_absorb_coh
    {ℓ ℓ' : Fact locs} {σ : State} (h : ℓ ⊑ ℓ')
    (hcoh : coh ℓ σ) : coh ℓ' σ := by
  unfold coh at *
  intro i hi
  apply hcoh
  apply Domain.ord_distr (i := i) at h
  simp [hi] at h
  assumption

/-! ## Bundled analysis -/

/-- A bundled `Flow.Analysis` for initialization, parameterized by
    the variable list, a `Nodup` proof, and the underlying CFG. -/
@[reducible]
def analysis {locs : List Loc} (hnd : locs.Nodup) (cfg : WFCFG) :
    Flow.Analysis (ls := dukeLangSem cfg) NodeID Edge State :=
  { dfa          := nDFA cfg locs
    botL         := _
    maxL         := _
    decEqL       := (inferInstance : DecidableEq (Fact locs))
    fhL          := _
    llL          := (inferInstance : LatticeLike (Fact locs))
    semantics    := semantics cfg hnd
    mono_absorb  := mono_absorb_coh
    transferMono := instTransferMonoN cfg }

/-- Wrapper around `Flow.analyze`: run the bundled
    analysis directly on a `CFG`. -/
def analyzeCFG {locs : List Loc} (hnd : locs.Nodup)
    (cfg : WFCFG) :
    Flow.AnalysisResult (analysis hnd cfg) :=
  Flow.analyze (analysis hnd cfg)

/-- Turn-key correctness for the bundled analysis: at every reachable
    program point, the computed in fact correctly approximates the
    concrete state. -/
theorem reachable_correct
    {locs : List Loc} (hnd : locs.Nodup)
    (cfg : WFCFG) :
    ∀ {n : NodeID} {σ : State},
      Flow.Analysis.Generic.Reachable cfg.analysis n σ State.isInit ->
      coh ((analyzeCFG hnd cfg).inFacts n) σ := by
  intro n σ hreach
  let A := analysis hnd cfg
  let R := analyzeCFG hnd cfg
  letI := A.maxL
  exact Flow.Analysis.Generic.reachable_corr
    cfg.analysis
    A.semantics
    A.mono_absorb
    R.isPostFix
    R.inFacts_entry
    hreach

def checkExpr {locs : List Loc} (ℓ : Fact locs) (e : Expr) : Bool :=
  evalExpr locs ℓ e == false

def checkNode {locs : List Loc} (ℓ : Fact locs) : NodeKind → Bool
  | .Skip => true
  | .Assign _ e => checkExpr ℓ e
  | .Assume e => checkExpr ℓ e

def checkCFG (cfg : WFCFG) : Bool :=
  let locs := vars cfg
  let res := (analyzeCFG locs.prop cfg).inFacts
  (List.range cfg.val.nodes.length).all fun n =>
    match cfg.val.nodeKind n with
    | none => false
    | some kind => checkNode (res n) kind

end Duke.Analysis.Initialization

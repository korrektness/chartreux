import Chartreux.Analysis.Generic
import Chartreux.Analysis.Worklist
import Chartreux.Analysis.WorklistProofs
import Chartreux.Duke.Eval
import Chartreux.Duke.CFG
import Chartreux.Duke.Utils
import Mathlib.Data.List.Nodup

namespace Duke.Analysis.Initialization

abbrev Loc := String

open Chartreux.Analysis
open Chartreux.Analysis.Generic

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

def evalExpr (locs : List Loc) (ρ : Fact locs) : Expr → Bool
  | .Null => false
  | .Int _ => false
  | .Var x =>
      match locs.finIdxOf? x with
      | none   => true
      | some i => ρ i
  | .IsNull e => evalExpr locs ρ e
  | .Not e => evalExpr locs ρ e
  | .BinOp _ e₁ e₂ => evalExpr locs ρ e₁ ⊔ evalExpr locs ρ e₂

def nodeTransfer (locs : List Loc) (g : CFG) (n : NodeID) :
    Fact locs -> Fact locs := fun ρ =>
  match g.nodeKind n with
  | some (.Assign x _) =>
    match locs.finIdxOf? x with
    | none   => ρ
    | some i => fun j => if j = i then false else ρ j
  | some (.Assume _) | some .Skip | none => ρ

def edgeTransfer (vars : List String) : Edge -> Fact vars -> Fact vars :=
  fun _ a => a

/-- The default initial fact: every tracked variable is uninitialized. -/
def entryInit (locs : List Loc) : Fact locs := fun _ => true

/-! ### Transfer function monotonicity -/

variable (cfg : WFCFG)
variable {locs : List Loc}

private lemma nodeTransfer_mono (n : NodeID) :
    mono_f (nodeTransfer locs cfg n) := by
  intro ρ₁ ρ₂ hxy
  funext j
  change (nodeTransfer locs cfg n ρ₁) j ⊑ (nodeTransfer locs cfg n ρ₂) j
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

/-! ## Correspondence predicate for concrete and abstract states -/

/-- For each variable, if the analysis tells us it is initialized, the concrete value exists -/
def corr (ℓ : Fact locs) (σ : State) : Prop :=
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
    (hnone : locs.finIdxOf? x = none) (hcorr : corr ℓ σ) :
    corr ℓ (σ.updated x v) := by
  simp only [corr, State.updated] at *
  grind [List.finIdxOf?_eq_none_iff]

@[simp] private lemma DFA_transferAlong (cfg : WFCFG)
    (e : EdgeOf cfg.analysis) (ℓ : Fact locs) :
    (nDFA cfg locs).transferAlong cfg.analysis e ℓ =
    nodeTransfer locs cfg e.val.src ℓ := rfl

/-- The `DFASemantics` for a fixed CFG. The three preservation
    fields directly consume the abstract `LangSem` transitions. -/
def semantics (hnd : locs.Nodup) :
    DFASemantics (ls := dukeLangSem cfg) cfg.analysis (nDFA cfg locs) :=
  { Corr := corr
    isInit := State.isInit
    preserve_entry := by
      intro σ hinit
      cases hinit
      simp [corr, State.empty, entryInit]
    preserve_step := by
      intro e σ σ' ℓ hstep hcorr
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
            apply hcorr; assumption
    preserve_stutter := by
      intro _n σ σ' ℓ hstut hcorr
      simp only [LangSem.LStutter] at hstut
      subst hstut
      assumption
  }

theorem mono_absorb_corr
    {ℓ ℓ' : Fact locs} {σ : State} (h : ℓ ⊑ ℓ')
    (hcorr : corr ℓ σ) : corr ℓ' σ := by
  unfold corr at *
  intro i hi
  apply hcorr
  apply Domain.ord_distr (i := i) at h
  simp [hi] at h
  assumption

/-! ## Bundled analysis -/

/-- A bundled `Chartreux.Analysis` for initialization, parameterized by
    the variable list, a `Nodup` proof, and the underlying CFG. -/
@[reducible]
def analysis {locs : List Loc} (hnd : locs.Nodup) (cfg : WFCFG) :
    Chartreux.Analysis (ls := dukeLangSem cfg) NodeID Edge State :=
  { dfa          := nDFA cfg locs
    botL         := _
    maxL         := _
    decEqL       := (inferInstance : DecidableEq (Fact locs))
    fhL          := _
    llL          := (inferInstance : LatticeLike (Fact locs))
    semantics    := semantics cfg hnd
    mono_absorb  := mono_absorb_corr
    transferMono := instTransferMonoN cfg }

/-- Wrapper around `Chartreux.analyze`: run the bundled
    analysis directly on a `CFG`. -/
def analyzeCFG {locs : List Loc} (hnd : locs.Nodup)
    (cfg : WFCFG) :
    Chartreux.AnalysisResult (analysis hnd cfg) :=
  Chartreux.analyze (analysis hnd cfg)

/-- Turn-key correctness for the bundled analysis: at every reachable
    program point, the computed in fact correctly approximates the
    concrete state. -/
theorem reachable_correct
    {locs : List Loc} (hnd : locs.Nodup)
    (cfg : WFCFG) :
    ∀ {n : NodeID} {σ : State},
      Chartreux.Analysis.Generic.Reachable cfg.analysis n σ State.isInit ->
      corr ((analyzeCFG hnd cfg).inFacts n) σ := by
  intro n σ hreach
  let A := analysis hnd cfg
  let R := analyzeCFG hnd cfg
  letI := A.maxL
  exact Chartreux.Analysis.Generic.reachable_corr
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

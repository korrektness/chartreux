import Chartreux.Analysis.Generic
import Chartreux.Analysis.Worklist
import Chartreux.Analysis.WorklistProofs
import Chartreux.Duke.Eval
import Chartreux.Duke.CFG
import Chartreux.Duke.Utils
import Mathlib.Tactic.Common

namespace Duke.Analysis.Initialization

open Chartreux.Analysis
open Chartreux.Analysis.Generic

/-! ## Lattice definition -/

/-- For each location, is it uninitialized?
    (false - initialized, true - uninitialized)
-/
abbrev Fact (locs : Nat) : Type := Domain locs Bool

def formatFact (mapping : Mapping) (locs : Nat) (ℓ : Fact locs) : String :=
  let parts : List String :=
    (List.finRange locs).filterMap fun i =>
      let isUninitialized := ℓ i
      if isUninitialized then some (mapping.get i) else none
  "uninit[" ++ String.intercalate ", " parts ++ "]"

/-! ## CFG transition functions -/

def evalExpr (locs : Nat) (ℓ : Fact locs) : NExpr → Bool
  | .Null => false
  | .Int _ => false
  | .Var x =>
      if h : x < locs then
        ℓ (Fin.mk x h)
      else
        true
  | .IsNull e => evalExpr locs ℓ e
  | .Not e => evalExpr locs ℓ e
  | .BinOp _ e₁ e₂ => evalExpr locs ℓ e₁ ⊔ evalExpr locs ℓ e₂

def nodeTransfer (locs : Nat) (g : CFG) (n : NodeID) :
    Fact locs -> Fact locs := fun ℓ =>
  match g.nodeKind n with
  | some (.Declare x (some _)) | some (.Assign x _) =>
    fun y => if y = x then false else ℓ y
  | some (.Declare x none) =>
    fun y => if y = x then true else ℓ y
  | some (.Assume _) | some .Skip | some .BlockEnter | some .BlockExit | none => ℓ

def edgeTransfer (locs : Nat) : Edge -> Fact locs -> Fact locs :=
  fun _ a => a

/-- The default initial fact: every tracked variable is uninitialized. -/
def entryInit (locs : Nat) : Fact locs := fun _ => true

/-! ### Transfer function monotonicity
    Technically not needed. But it being true implies that the result is the least post-fixpoint
-/

variable (cfg : WFCFG)
variable {locs : Nat}

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
    cases k with (try simp only; try grind [Domain.ord_distr hxy])
    | Declare x e =>
      cases e <;> simp only
      · split_ifs
        · simp [max]
        · apply Domain.ord_distr
          assumption
      · split_ifs
        · simp [max]
        · apply Domain.ord_distr
          assumption
    | Assign x e =>
      split_ifs
      · simp [max]
      · apply Domain.ord_distr
        assumption

private lemma edgeTransfer_mono :
    ∀ e, mono_f (edgeTransfer locs e) := fun _ _ _ h => h

/-! ## Coherence predicate for concrete and abstract states -/

/-- For each variable, if the analysis tells us it is initialized, the concrete value exists -/
def coh (ℓ : Fact locs) (σ : NState) : Prop :=
  ∀ i,
    ℓ i = false ->
    ∃ v, σ i = .declared (some v)

/-- The DFA closure for initialization, parameterised by the underlying CFG.
    The CFG is needed to read `nodeKind`. -/
@[reducible]
def nDFA (locs : Nat) : DFA NodeID Edge where
  L            := Fact locs
  nodeTransfer := nodeTransfer locs cfg
  edgeTransfer := edgeTransfer locs
  entry        := entryInit locs


@[simp] private lemma DFA_transferAlong (cfg : WFCFG)
    (e : EdgeOf cfg.analysis) (ℓ : Fact locs) :
    (nDFA cfg locs).transferAlong cfg.analysis e ℓ =
    nodeTransfer locs cfg e.val.src ℓ := rfl

/-- The `DFASemantics` for a fixed CFG. The three preservation
    fields directly consume the abstract `LangSem` transitions. -/
def semantics :
    DFASemantics (ls := dukeLangSem cfg) cfg.analysis (nDFA cfg locs) :=
  { Coh := coh
    preserve_entry := by
      intro σ hinit
      cases hinit
      simp [coh, State.empty, entryInit]
    preserve_step := by
      intro e σ σ' ℓ hstep hcoh
      simp only [DFA_transferAlong, nodeTransfer]
      cases hstep with simp only [*]
      | @declare =>
        unfold coh State.declared State.set at *
        intros i hi
        simp only at hi
        split at hi <;> try contradiction
        grind
      | @declareVal _ _ x expr v _ _ _ _ _ _ hdecl hupd =>
        intro j habs
        simp only at habs
        split_ifs at habs
        · subst_vars
          constructor
          rw [State.updated_eq hupd]
        · have hxj : x ≠ j := by grind
          rw [State.updated_neq hxj hupd]
          rw [State.declared_neq hxj hdecl]
          apply hcoh; assumption
      | @assign _ _ x expr v _ _ _ _ _ hupd =>
        intro j habs
        simp only at habs
        split_ifs at habs
        · subst_vars
          constructor
          rw [State.updated_eq hupd]
        · have hxj : x ≠ j := by grind
          rw [State.updated_neq hxj hupd]
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

/-- A bundled `Chartreux.Analysis` for initialization, parameterized by
    the variable list, a `Nodup` proof, and the underlying CFG. -/
@[reducible]
def analysis {locs : Nat} (cfg : WFCFG) :
    Chartreux.Analysis (ls := dukeLangSem cfg) NodeID Edge State :=
  { dfa          := nDFA cfg locs
    botL         := (inferInstance : Bot (Fact locs))
    maxL         := _
    decEqL       := (inferInstance : DecidableEq (Fact locs))
    fhL          := (inferInstance : FiniteHeight (Fact locs))
    llL          := (inferInstance : SemiLattice (Fact locs))
    semantics    := semantics cfg
    mono_absorb  := mono_absorb_coh
    edge_mono    := edgeTransfer_mono }

/-- Wrapper around `Chartreux.analyze`: run the bundled
    analysis directly on a `CFG`. -/
def analyzeCFG {locs : Nat} (cfg : WFCFG) :
    Chartreux.AnalysisResult (@analysis locs cfg) :=
  Chartreux.analyze (analysis cfg)

/-- Turn-key correctness for the bundled analysis: at every reachable
    program point, the computed in fact correctly approximates the
    concrete state. -/
theorem reachable_correct {locs : Nat} (cfg : WFCFG) :
    ∀ {n : NodeID} {σ : State},
      Chartreux.Analysis.Generic.Reachable cfg.analysis n σ State.isInit ->
      coh ((@analyzeCFG locs cfg).inFacts n) σ := by
  intro n σ hreach
  let A := @analysis locs cfg
  let R := @analyzeCFG locs cfg
  letI := A.maxL
  exact Chartreux.Analysis.Generic.reachable_corr
    cfg.analysis
    A.semantics
    A.mono_absorb
    R.isPostFix
    R.inFacts_entry
    hreach

def checkExpr {locs : Nat} (ℓ : Fact locs) (e : NExpr) : Bool :=
  evalExpr locs ℓ e == false

def checkNode {locs : Nat} (ℓ : Fact locs) : NodeKind → Bool
  | .Skip | .BlockEnter | .BlockExit | .Declare _ none => true
  | .Declare _ (some e) | .Assign _ e | .Assume e => checkExpr ℓ e

def checkCFG (cfg : WFCFG) : Bool :=
  let locs := totalVars cfg
  let res := (@analyzeCFG locs cfg).inFacts
  (List.range cfg.val.nodes.length).all fun n =>
    match cfg.val.nodeKind n with
    | none => false
    | some kind => checkNode (res n) kind

end Duke.Analysis.Initialization

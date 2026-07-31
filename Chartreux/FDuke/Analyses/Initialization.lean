import Chartreux.Analysis.Generic
import Chartreux.Analysis.Worklist
import Chartreux.Analysis.WorklistProofs
import Chartreux.FDuke.Eval
import Chartreux.FDuke.CFG
import Chartreux.FDuke.Refinement
import Mathlib.Data.List.Nodup

section Utils
namespace List

variable {α : Type} (x : α) (l : List α)
variable [DecidableEq α]

theorem finIdxOf?_nodup (hnd : l.Nodup)
    (i j : Fin l.length) (hi : l.finIdxOf? x = some i) (hneq : j ≠ i) :
    x ≠ l.get j := by
  intro h_eq
  have hget := List.finIdxOf?_eq_some_iff.mp hi |>.left
  subst h_eq
  rw [List.get_eq_getElem] at *
  have := (List.getElem_inj hnd).1 hget
  grind

end List
end Utils

namespace FDuke.Analysis.Initialization

abbrev Loc := String

open Chartreux.Analysis
open Chartreux.Analysis.Generic
open FDuke.Refinement

/-! ## Lattice definition -/

/-- (x : Var) |-> "is x initialized?" -/
abbrev Fact (locs : List Loc) : Type := Domain locs.length Bool

def formatFact (locs : List Loc) (ℓ : Fact locs) : String :=
  let parts : List String :=
    (List.finRange locs.length).filterMap fun i =>
      let isUninitialized := ℓ i
      if isUninitialized then some (locs.get i) else none
  "uninit[" ++ String.intercalate ", " parts ++ "]"

/-! ## CFG transition functions -/

def evalExpr (locs : List Loc) (ℓ : Fact locs) : FExpr → Bool
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
  | _ => ℓ

def edgeTransfer (vars : List String) : Edge -> Fact vars -> Fact vars :=
  fun _ a => a

/-- The default initial fact: every tracked variable is uninitialized. -/
def entryInit (locs : List Loc) : Fact locs := fun _ => true

/-! ### Transfer function monotonicity
    Technically not needed. But it being true implies that the result is the least post-fixpoint
-/

variable (cfg : WFCFG)
variable {locs : List Loc}

private lemma nodeTransfer_mono (n : NodeID) :
    mono_f (nodeTransfer locs cfg.kappa n) := by
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
  nodeTransfer := nodeTransfer locs cfg.kappa
  edgeTransfer := edgeTransfer locs
  entry        := entryInit locs

private lemma preserve_update_none (ℓ : Fact locs)
    (hnone : locs.finIdxOf? x = none) (hcoh : coh ℓ σ) :
    coh ℓ (σ.updated x v) := by
  simp only [coh, State.updated] at *
  grind [List.finIdxOf?_eq_none_iff]

@[simp] private lemma DFA_transferAlong (cfg : WFCFG)
    (e : EdgeOf cfg.kappa.analysis) (ℓ : Fact locs) :
    (nDFA cfg.kappa locs).transferAlong cfg.kappa.analysis e ℓ =
    nodeTransfer locs cfg.kappa e.val.src ℓ := rfl

/-- The `DFASemantics` for a fixed CFG. The three preservation
    fields directly consume the abstract `LangSem` transitions. -/
def semantics (hnd : locs.Nodup) :
    DFASemantics (ls := kappaLangSem cfg) cfg.kappa.analysis (nDFA cfg.kappa locs) :=
  { Coh := coh
    preserve_entry := by
      intro σ hinit
      cases hinit
      simp [coh, State.empty, entryInit]
    preserve_step := by
      intro e σ σ' ℓ hstep hcoh
      simp only [DFA_transferAlong, nodeTransfer]
      have hκ : cfg.kappa.val.nodeKind e.val.src = cfg.val.nodeKind e.val.src :=
        CFG.kappa_nodeKind cfg e.val.src
      generalize hk : cfg.kappa.val.nodeKind e.val.src = k
      cases hstep with
      | inr l =>
        obtain ⟨⟨f, lam, h⟩, rfl⟩ := l
        grind
      | inl l =>
        rcases l with hassign|h|h|h
        · obtain ⟨x, e', v, hkind, heval, rfl⟩ := hassign
          rw [<- hκ, hk] at hkind
          simp only [hkind]
          split
          · apply preserve_update_none <;> trivial
          · intros i hi
            simp only at hi
            split_ifs at hi
            · subst i
              rename_i heq
              have hget := List.finIdxOf?_eq_some_iff.mp heq |>.left
              rw [Fin.getElem_fin] at hget
              rw [List.get_eq_getElem, hget, State.updated_eq σ x v]
              rfl
            · have h_x_neq : x ≠ locs.get i := by
                apply List.finIdxOf?_nodup <;> trivial
              rw [State.updated_neq (hne := h_x_neq)]
              apply hcoh; trivial
        all_goals -- ew
          obtain ⟨_, _, _, _, _⟩ := h
          grind
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
def analysis {locs : List Loc} (hnd : locs.Nodup) (cfg : WFCFG) :
    Chartreux.Analysis (ls := kappaLangSem cfg) NodeID Edge State :=
  { dfa          := nDFA cfg locs
    botL         := (inferInstance : Bot (Fact locs))
    maxL         := _
    decEqL       := (inferInstance : DecidableEq (Fact locs))
    fhL          := (inferInstance : FiniteHeight (Fact locs))
    llL          := (inferInstance : SemiLattice (Fact locs))
    semantics    := semantics cfg hnd
    mono_absorb  := mono_absorb_coh
    edge_mono    := edgeTransfer_mono }

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
      coh ((analyzeCFG hnd cfg).inFacts n) σ := by
  intro n σ hreach
  let A := analysis hnd cfg
  let R := analyzeCFG hnd cfg
  letI := A.maxL
  exact kappa_rewrite_correct
    cfg
    A.semantics
    A.mono_absorb
    R.isPostFix
    R.inFacts_entry
    hreach

def checkExpr {locs : List Loc} (ℓ : Fact locs) (e : FExpr) : Bool :=
  evalExpr locs ℓ e == false

def checkNode {locs : List Loc} (ℓ : Fact locs) : NodeKind → Bool
  | .Skip | .Call _ _ | .Invoke => true
  | .Assign _ e => checkExpr ℓ e
  | .Assume e => checkExpr ℓ e

def checkCFG (cfg : WFCFG) : Bool :=
  let locs := vars cfg
  let res := (analyzeCFG locs.prop cfg).inFacts
  (List.range cfg.val.nodes.length).all fun n =>
    match cfg.val.nodeKind n with
    | none => false
    | some kind => checkNode (res n) kind

end FDuke.Analysis.Initialization

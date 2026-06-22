import Flow.Analysis.Generic
import Flow.Analysis.Worklist
import Flow.Analysis.WorklistProofs
import Flow.Duke.Eval
import Flow.Duke.CFG
import Flow.Duke.Utils
import Mathlib.Data.List.Nodup

abbrev Loc := String

namespace Duke.Analysis.Nullability

open Flow.Analysis
open Flow.Analysis.Generic

/-! ## Lattice definition -/

/-- Abstract value for a single variable -/
inductive NVal where
  | nonnull
  | top
deriving DecidableEq, Repr

instance : ToString NVal where
  toString
    | .nonnull => "nonnull"
    | .top     => "⊤"

instance {v : List String} : ToString (Domain v.length NVal) where
  toString ρ :=
    let parts : List String :=
      (List.finRange v.length).map fun i =>
        v.get i ++ "=" ++ toString (ρ i)
    "[" ++ String.intercalate ", " parts ++ "]"

instance : Bot NVal where
  bot := .nonnull

instance : Max NVal where
  max
    | .nonnull, .nonnull => .nonnull
    | _, _               => .top

/-- `FiniteHeight` for NVal : bounded by 2. -/
instance : FiniteHeight NVal where
  remainingHeight
    | .top => 0
    | .nonnull => 1
  height_join a b h := by
    cases a <;> cases b <;> try contradiction
    simp

instance : LatticeLike NVal where
  join_comm  := by intro a b; cases a <;> cases b <;> rfl
  join_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  join_idem  := by intro a; cases a <;> rfl
  bot_le     := by intro a; cases a <;> rfl

/-! ## CFG transition functions -/

/-- A nullability fact for a program with location `locs`
    is a `Domain` over `NVal`. -/
abbrev NFact (locs : List Loc) : Type := Domain locs.length NVal

def nonNullAssumption (e : Expr) : List Loc :=
  match e with
  | .BinOp .and e₁ e₂ => nonNullAssumption e₁ ++ nonNullAssumption e₂
  | .Not (.IsNull (.Var x)) => [x]
  | _ => []

def assumeExpr (locs : List Loc) (inFacts : NFact locs) (e : Expr) : NFact locs :=
  let nonNull := nonNullAssumption e |>.filterMap locs.finIdxOf?
  fun j => if nonNull.contains j then .nonnull else inFacts j

def evalExpr (locs : List Loc) (ρ : NFact locs) : Expr → NVal
  | .Null => .top
  | .Int _ => .nonnull
  | .Var x =>
      match  locs.finIdxOf? x with
      | none   => .top
      | some i => ρ i
  | .IsNull e => evalExpr locs ρ e
  | .Not e => evalExpr locs ρ e
  | .BinOp _ e₁ e₂ => evalExpr locs ρ e₁ ⊔ evalExpr locs ρ e₂

def nTransfer (locs : List Loc) (g : CFG) (n : NodeID) :
    NFact locs -> NFact locs := fun ρ =>
  match g.nodeKind n with
  | some (.Assign l e) =>
    match locs.finIdxOf? l with
    | none   => ρ
    | some i =>
        let v := evalExpr locs ρ e
        fun j => if j = i then v else ρ j
  | some (.Assume e) => assumeExpr locs ρ e
  | some .Skip | none => ρ

/-- Edge transfer for forward nullability is the identity. -/
def nEdgeTransfer (vars : List String) : Edge -> NFact vars -> NFact vars :=
  fun _ a => a

/-- The default initial fact: every tracked variable is `nonnull`. -/
def nEntryInit (locs : List Loc) : NFact locs := fun _ => .nonnull

/-! ### Transfer function monotonicity -/

variable (cfg : WFCFG)
variable {locs : List Loc}

private lemma assumeExpr_mono (ρ₁ ρ₂ : NFact locs)
    (hρ : ρ₁ ⊑ ρ₂) (e : Expr) :
    assumeExpr locs ρ₁ e ⊑ assumeExpr locs ρ₂ e := by
  unfold assumeExpr
  simp only
  funext j
  rw [Domain.max_app]
  split
  · apply LatticeLike.join_idem
  · grind [Domain.ord_distr hρ]

private lemma evalExpr_mono (ρ₁ ρ₂ : NFact locs)
    (hρ : ρ₁ ⊑ ρ₂) (e : Expr) :
    evalExpr locs ρ₁ e ⊑ evalExpr locs ρ₂ e := by
  induction e with simp only [evalExpr]
  | Null => grind [LatticeLike.join_idem]
  | Int n => grind [LatticeLike.join_idem]
  | Var x => grind [LatticeLike.join_idem, Domain.ord_distr hρ]
  | BinOp op e₁ e₂ ih₁ ih₂ =>
    cases ha₁ : evalExpr locs ρ₁ e₁ <;>
      cases hb₁ : evalExpr locs ρ₁ e₂ <;>
      cases ha₂ : evalExpr locs ρ₂ e₁ <;>
      cases hb₂ : evalExpr locs ρ₂ e₂ <;>
      rw [ha₁, ha₂] at ih₁ <;>
      rw [hb₁, hb₂] at ih₂ <;>
      simp_all [Max.max]
  | Not e => grind
  | IsNull e => grind

private lemma nTransfer_mono (n : NodeID) :
    mono_f (nTransfer locs cfg n) := by
  intro ρ₁ ρ₂ hxy
  funext j
  change (nTransfer locs cfg n ρ₁) j ⊑ (nTransfer locs cfg n ρ₂) j
  unfold nTransfer
  simp only
  generalize hk : cfg.val.nodeKind n = nk
  cases nk with
  | none => apply Domain.ord_distr; assumption
  | some k =>
    cases k with simp only
    | Skip => apply Domain.ord_distr; assumption
    | Assign x e =>
      generalize hx : locs.finIdxOf? x = a
      cases a <;> simp only <;> try split
      all_goals grind [Domain.ord_distr hxy, evalExpr_mono]
    | Assume e =>
      apply Domain.ord_distr
      apply assumeExpr_mono
      assumption

private lemma nEdgeTransfer_mono :
    ∀ e, mono_f (nEdgeTransfer locs e) := fun _ _ _ h => h

instance instTransferMonoN :
    TransferMono (nTransfer locs cfg) (nEdgeTransfer locs) where
  node_mono := nTransfer_mono cfg
  edge_mono := nEdgeTransfer_mono

/-! ## Correspondence predicate for concrete and abstract states -/

/-- For each variable, if the analysis tells us it is not null, the concrete value is not null -/
def ncorr (ℓ : NFact locs) (σ : State) : Prop :=
  ∀ i v,
    ℓ i = .nonnull ->
    σ (locs.get i) = some v ->
    v ≠ .Null

/-- The DFA closure for nullability, parameterised by the underlying CFG.
    The CFG is needed to read `nodeKind`. -/
def nDFA (locs : List Loc) : DFA NodeID Edge where
  L            := NFact locs
  nodeTransfer := nTransfer locs cfg
  edgeTransfer := nEdgeTransfer locs
  entry        := nEntryInit locs

lemma evalExpr_sound {locs : List Loc} {ℓ : NFact locs} {σ : State} {expr : Expr} {v : Val}
    (hcorr : ncorr ℓ σ)
    (heval : EvalExpr σ expr v)
    (h_abs : evalExpr locs ℓ expr = NVal.nonnull) : v ≠ Val.Null := by
  induction heval with simp! [evalExpr] at *
  | @var x v h =>
    split at h_abs <;> try contradiction
    rename_i hi
    apply hcorr <;> try trivial
    grind [List.finIdxOf?_eq_some_iff]

lemma nonNullAssumption_sound {locs : List Loc} {σ : State} {expr : Expr} {n : Int}
    {i : Fin locs.length}
    (heval : EvalExpr σ expr (Val.Int n))
    (htruthy : n ≠ 0)
    (hget : σ (locs.get i) = some Val.Null)
    (hass : locs.get i ∈ nonNullAssumption expr) :
    ∃ j, j < i ∧ locs.get j = locs.get i := by
  induction expr generalizing n with try contradiction
  | Not expr =>
    cases expr with try contradiction
    | IsNull expr =>
      cases expr with try contradiction
      | Var x =>
        simp! [nonNullAssumption] at hass
        subst hass
        cases heval with try contradiction
        | notF _ heval =>
          cases heval with try contradiction
          | isnullF _ _ heval =>
            cases heval with try contradiction
            | var => grind
  | BinOp op e₁ e₂ ih₁ ih₂ =>
    cases op with try contradiction
    | and =>
      cases heval with
      | binop _ _ _ n₁ n₂ eval₁ eval₂ =>
        have h1_neq : n₁ ≠ 0 := by grind [applyOp]
        have h2_neq : n₂ ≠ 0 := by grind [applyOp]
        simp! [nonNullAssumption] at hass
        cases hass <;> grind

lemma assumeExpr_sound {locs : List Loc} {ℓ : NFact locs} {σ : State} {expr : Expr} {n : Int}
    (hcorr : ncorr ℓ σ)
    (heval : EvalExpr σ expr (Val.Int n))
    (htruthy : n ≠ 0) :
    ncorr (assumeExpr locs ℓ expr) σ := by
  simp! [ncorr, assumeExpr]
  intro i v h henv rfl
  apply hcorr <;> try trivial
  apply h
  intro hass
  apply nonNullAssumption_sound <;> trivial

private lemma n_preserve_update_none (ℓ : NFact locs)
  (hnone : locs.finIdxOf? x = none) (hcorr : ncorr ℓ σ) :
  ncorr ℓ (σ.updated x v) := by
    intro j v' habs hupd hv'
    simp only [ncorr, State.updated, hv'] at *
    split at hupd <;> grind [List.finIdxOf?_eq_none_iff]

@[simp] private lemma nDFA_transferAlong (cfg : WFCFG)
    (e : EdgeOf cfg.analysis) (ℓ : NFact locs) :
    (nDFA cfg locs).transferAlong cfg.analysis e ℓ =
    nTransfer locs cfg e.val.src ℓ := rfl

/-- The nullability `DFASemantics` for a fixed CFG. The three preservation
    fields directly consume the abstract `LangSem` transitions. -/
def nSemantics (hnd : locs.Nodup) :
    DFASemantics (ls := dukeLangSem cfg) cfg.analysis (nDFA cfg locs) :=
  { Corr := ncorr
    isInit := State.isInit
    preserve_entry := by
      intro σ hinit
      cases hinit
      simp [ncorr, nDFA, State.empty]
    preserve_step := by
      intro e σ σ' ℓ hstep hcorr
      simp only [nDFA_transferAlong, nTransfer, CFG.nodeKind]
      cases hstep with simp only [*]
      | assign _ heval _ =>
        rename_i x expr v _ _
        split
        · apply n_preserve_update_none <;> trivial
        · intro k v' h hupd hv'
          subst hv'
          simp only at h
          split_ifs at h
          · subst k
            rename_i i hi
            have hget := List.finIdxOf?_eq_some_iff.mp hi |>.left
            rw [Fin.getElem_fin] at hget
            rw [List.get_eq_getElem, hget, State.updated_eq σ x v] at hupd
            have h_v_not_null : v ≠ Val.Null := evalExpr_sound hcorr heval h
            grind
          · have h_x_neq : x ≠ locs.get k := by apply List.finIdxOf?_nodup <;> trivial
            rw [State.updated_neq] at hupd <;> try trivial
            apply hcorr <;> trivial
      | @assum _ _ n _ _ _ heval htruthy _ =>
        have : n ≠ 0 := by grind
        apply assumeExpr_sound <;> trivial
    preserve_stutter := by
      intro _n σ σ' ℓ hstut hcorr
      simp only [LangSem.LStutter] at hstut
      subst hstut
      assumption
  }

theorem mono_absorb_corr
    {ℓ ℓ' : NFact locs} {σ : State} (h : ℓ ⊑ ℓ')
    (hcorr : ncorr ℓ σ) : ncorr ℓ' σ := by
  simp only [ncorr] at *
  intros i v habs
  have hi : ℓ i ⊑ ℓ' i := Domain.ord_distr h
  rw [habs] at hi
  simp only [max] at hi
  generalize heq : ℓ i = x at hi
  cases x <;> grind

/-! ## Bundled Nullability analysis -/

/-- A bundled `Flow.Analysis` for nullability, parameterized by
    the variable list, a `Nodup` proof, and the underlying CFG. -/
def nAnalysis {locs : List Loc} (hnd : locs.Nodup) (cfg : WFCFG) :
    Flow.Analysis (ls := dukeLangSem cfg) NodeID Edge State :=
  { dfa          := nDFA cfg locs
    botL         := _
    maxL         := _
    decEqL       := (inferInstance : DecidableEq (NFact locs))
    fhL          := _
    llL          := (inferInstance : LatticeLike (NFact locs))
    semantics    := nSemantics cfg hnd
    mono_absorb  := mono_absorb_corr
    transferMono := instTransferMonoN cfg }

/-- TIP-facing wrapper around `Flow.analyze`: run the bundled Nullability
    analysis directly on a `CFG`. -/
def nAnalyzeCFG {locs : List Loc} (hnd : locs.Nodup)
    (cfg : WFCFG) :
    Flow.AnalysisResult (nAnalysis hnd cfg) :=
  Flow.analyze (nAnalysis hnd cfg)

/-- Turn-key correctness for the bundled nullability analysis: at every reachable
    program point, the computed in fact correctly approximates the
    /oncrete state. -/
theorem nreachable_correct
    {locs : List Loc} (hnd : locs.Nodup)
    (cfg : WFCFG) :
    ∀ {n : NodeID} {σ : State},
      Flow.Analysis.Generic.Reachable cfg.analysis n σ State.isInit ->
      ncorr ((nAnalyzeCFG hnd cfg).inFacts n) σ := by
  intro n σ hreach
  let A := nAnalysis hnd cfg
  let R := nAnalyzeCFG hnd cfg
  letI := A.maxL
  exact Flow.Analysis.Generic.reachable_corr
    cfg.analysis
    A.semantics
    A.mono_absorb
    R.isPostFix
    R.inFacts_entry
    hreach

end Duke.Analysis.Nullability

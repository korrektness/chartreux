import Flow.Analysis.Generic
import Flow.Analysis.Worklist
import Flow.Analysis.WorklistProofs
import Flow.Duke.Eval
import Flow.Duke.CFG
import Flow.Duke.Utils
import Mathlib.Data.List.Nodup

namespace Duke.Analysis.Nullability

abbrev Loc := String

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

/-- A nullability witness for other variables -/
abbrev NWitness (locs : List Loc) : Type := Domain locs.length NVal
def emptyWitness (locs : List Loc) : NWitness locs := fun _ => .top

/-- A nullability fact for a program with location `locs`
    is a `Domain` over
    * `NVal` - am I null?
    * `NWitness` - do I carry the proof that others are null?
-/
abbrev NFact (locs : List Loc) : Type := Domain locs.length (NVal × NWitness locs)

def extractWitnesses (locs : List Loc) (wit : NWitness locs) : List Loc :=
  (List.finRange locs.length).filterMap (
    fun i => match wit i with
             | .nonnull => some (locs.get i)
             | _ => none
  )

/-- Pretty-print a witness map using variable names: the set of locations
    that this witness currently proves to be non-null. -/
def formatNWitness (witnesses : List Loc) : String :=
  "{" ++ String.intercalate ", " witnesses ++ "}"

/-- Pretty-print a nullability fact using variable names. For each tracked
    variable we show its abstract nullability value and the set of variables
    it witnesses as non-null. -/
def formatNFact (locs : List Loc) (ℓ : NFact locs) : String :=
  let parts : List String :=
    (List.finRange locs.length).map fun i =>
      let (v, wit) := ℓ i
      let witnesses := extractWitnesses locs wit
      s!"{locs.get i}={v}" ++ if witnesses.isEmpty then "" else s!" ⇒ {formatNWitness witnesses}"
  "[" ++ String.intercalate ", " parts ++ "]"

def nonNullAssumption (locs : List Loc) (inFacts : NFact locs) (e : Expr) : List Loc :=
  match e with
  | .BinOp .and e₁ e₂ => nonNullAssumption locs inFacts e₁ ++ nonNullAssumption locs inFacts e₂
  | .Not (.IsNull (.Var x)) => [x]
  | .Var x =>
      match locs.finIdxOf? x with
      | none   => []
      | some i => inFacts i |>.snd |> extractWitnesses locs
  | _ => []

/-- What does this expression witness? -/
def exprWitness (locs : List Loc) (inFacts : NFact locs) (e : Expr) : NWitness locs :=
  let nonNull := nonNullAssumption locs inFacts e |>.filterMap locs.finIdxOf?
  fun j => if nonNull.contains j then .nonnull else .top

def evalExpr (locs : List Loc) (ρ : NFact locs) : Expr → NVal
  | .Null => .top
  | .Int _ => .nonnull
  | .Var x =>
      match locs.finIdxOf? x with
      | none   => .top
      | some i => ρ i |>.fst
  | .IsNull _ => .nonnull
  | .Not _ => .nonnull
  | .BinOp _ e₁ e₂ => evalExpr locs ρ e₁ ⊔ evalExpr locs ρ e₂

def nTransfer (locs : List Loc) (g : CFG) (n : NodeID) :
    NFact locs -> NFact locs := fun ρ =>
  match g.nodeKind n with
  | some (.Assign l e) =>
    match locs.finIdxOf? l with
    | none   => ρ
    | some i =>
        let v := evalExpr locs ρ e
        let wit := exprWitness locs ρ e
        -- mutation might have invalidated some of the witnesses
        -- we could be smart about just invalidating relevant ones,
        -- but for now we just invalidate all of them.
        -- TODO: invalidate only relevant bits
        fun j => if j = i then (v, wit) else (ρ j |>.fst, emptyWitness locs)
  | some (.Assume e) =>
    let wit := exprWitness locs ρ e
    -- we preserve the witnesses from before, but update the nullability status
    fun i => (if wit i == .nonnull then .nonnull else ρ i |>.fst, ρ i |>.snd)
  | some .Skip | none => ρ

/-- Edge transfer for forward nullability is the identity. -/
def nEdgeTransfer (vars : List String) : Edge -> NFact vars -> NFact vars :=
  fun _ a => a

/-- The default initial fact: every tracked variable is `nonnull` and carries witnesses. -/
def nEntryInit (locs : List Loc) : NFact locs := fun _ => (.nonnull, emptyWitness locs)

/-! ### Transfer function monotonicity -/

variable (cfg : WFCFG)
variable {locs : List Loc}

private lemma extractWitnesses_incl (ρ₁ ρ₂ : NWitness locs)
    (hρ : ρ₁ ⊑ ρ₂) (l : Loc) :
    l ∈ extractWitnesses locs ρ₂ -> l ∈ extractWitnesses locs ρ₁ := by
  unfold extractWitnesses
  intro h
  rw [List.mem_filterMap] at *
  have ⟨i, hin, heq⟩ := h
  use i
  apply Domain.ord_distr (i := i) at hρ
  generalize h1 : ρ₁ i = x₁ at *
  generalize h2 : ρ₂ i = x₂ at *
  cases x₁ <;> cases x₂ <;> trivial

private lemma nonNullAssumption_incl (ρ₁ ρ₂ : NFact locs)
    (hρ : ρ₁ ⊑ ρ₂) (e : Expr) (l : Loc) :
    l ∈ nonNullAssumption locs ρ₂ e -> l ∈ nonNullAssumption locs ρ₁ e := by
  induction e generalizing l with try grind [nonNullAssumption]
  | Not e => unfold nonNullAssumption at *; grind
  | BinOp op e₁ e₂ ih₁ ih₂ =>
    intro hin
    cases op <;> grind [nonNullAssumption]
  | Var x =>
    simp [nonNullAssumption]
    split <;> try grind
    rename_i i _
    apply extractWitnesses_incl
    exact congrArg (fun ρ => (ρ i).snd) hρ

private lemma exprWitness_mono (ρ₁ ρ₂ : NFact locs)
    (hρ : ρ₁ ⊑ ρ₂) (e : Expr) :
    exprWitness locs ρ₁ e ⊑ exprWitness locs ρ₂ e := by
  unfold exprWitness
  simp only
  funext j
  rw [Domain.max_app]
  repeat split <;> try rfl
  rename_i hneg hpos
  absurd hneg
  rw [List.contains_iff_mem, List.mem_filterMap] at *
  grind [nonNullAssumption_incl]

private lemma evalExpr_mono (ρ₁ ρ₂ : NFact locs)
    (hρ : ρ₁ ⊑ ρ₂) (e : Expr) :
    evalExpr locs ρ₁ e ⊑ evalExpr locs ρ₂ e := by
  induction e with (simp only [evalExpr]; try grind [LatticeLike.join_idem])
  | Var x =>
    split <;> try rfl
    rename_i i _
    exact congrArg (fun ρ => (ρ i).fst) hρ
  | BinOp op e₁ e₂ ih₁ ih₂ =>
    cases ha₁ : evalExpr locs ρ₁ e₁ <;>
      cases hb₁ : evalExpr locs ρ₁ e₂ <;>
      cases ha₂ : evalExpr locs ρ₂ e₁ <;>
      cases hb₂ : evalExpr locs ρ₂ e₂ <;>
      rw [ha₁, ha₂] at ih₁ <;>
      rw [hb₁, hb₂] at ih₂ <;>
      simp_all [Max.max]

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
      · apply Domain.ord_distr
        assumption
      · ext
        case fst =>
          apply evalExpr_mono
          assumption
        case h k =>
          apply Domain.ord_distr
          apply exprWitness_mono
          assumption
      · ext
        case fst => exact congrArg (fun ρ => (ρ j).fst) hxy
        case h k => rfl
    | Assume e =>
      ext
      case fst =>
        have hw_mono := Domain.ord_distr (exprWitness_mono ρ₁ ρ₂ hxy e) (i := j)
        generalize hw1 : exprWitness locs ρ₁ e j = w₁ at *
        generalize hw2 : exprWitness locs ρ₂ e j = w₂ at *
        cases w₁ <;> cases w₂ <;> simp [Max.max] at * <;> grind
      case h i =>
        apply Domain.ord_distr
        exact congrArg (fun ρ => (ρ j).snd) hxy

private lemma nEdgeTransfer_mono :
    ∀ e, mono_f (nEdgeTransfer locs e) := fun _ _ _ h => h

instance instTransferMonoN :
    TransferMono (nTransfer locs cfg) (nEdgeTransfer locs) where
  node_mono := nTransfer_mono cfg
  edge_mono := nEdgeTransfer_mono

/-! ## Correspondence predicate for concrete and abstract states -/

/-- For each variable, if the analysis tells us it is not null, the concrete value is not null -/
def ncorr_self (ℓ : NFact locs) (σ : State) : Prop :=
  ∀ i v,
    (ℓ i).fst = .nonnull ->
    σ (locs.get i) = some v ->
    v ≠ .Null
/-- Variable `i` is the witness that variable `j` is not null -/
def ncorr_wit (ℓ : NFact locs) (σ : State) : Prop :=
  ∀ i j n v,
    (ℓ i).snd j = .nonnull ->
    σ (locs.get i) = some (.Int n) ->
    n ≠ 0 -> -- if variable `i` is truthy
    σ (locs.get j) = some v ->
    v ≠ .Null

def ncorr (ℓ : NFact locs) (σ : State) : Prop := ncorr_self ℓ σ ∧ ncorr_wit ℓ σ

/-- The DFA closure for nullability, parameterised by the underlying CFG.
    The CFG is needed to read `nodeKind`. -/
@[reducible]
def nDFA (locs : List Loc) : DFA NodeID Edge where
  L            := NFact locs
  nodeTransfer := nTransfer locs cfg
  edgeTransfer := nEdgeTransfer locs
  entry        := nEntryInit locs

lemma evalExpr_sound {locs : List Loc} {ℓ : NFact locs} {σ : State} {expr : Expr} {v : Val}
    (hcorr : ncorr_self ℓ σ)
    (heval : EvalExpr σ expr v)
    (h_abs : evalExpr locs ℓ expr = NVal.nonnull) : v ≠ Val.Null := by
  induction heval with simp! [evalExpr] at *
  | @var x v h =>
    split at h_abs <;> try contradiction
    rename_i hi
    apply hcorr <;> try trivial
    grind [List.finIdxOf?_eq_some_iff]

lemma nonNullAssumption_sound {locs : List Loc} {ℓ : NFact locs} {σ : State} {expr : Expr} {n : Int}
    {i : Fin locs.length}
    (hcorr : ncorr ℓ σ)
    (heval : EvalExpr σ expr (Val.Int n))
    (htruthy : n ≠ 0)
    (hget : σ (locs.get i) = some Val.Null) :
    locs.get i ∉ nonNullAssumption locs ℓ expr := by
  induction expr generalizing n with (intro hass; try contradiction)
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
  | Var x =>
    simp! [nonNullAssumption, extractWitnesses] at hass
    split at hass <;> try trivial
    rename_i j hin
    have ⟨rfl, _⟩ := List.finIdxOf?_eq_some_iff.mp hin
    cases heval with
    | var _ _ h_sig =>
      simp only [List.mem_filterMap, List.mem_finRange, true_and] at hass
      obtain ⟨a, ha⟩ := hass
      cases h_snd : (ℓ j).snd a <;> simp [h_snd] at ha
      apply hcorr.right <;> try trivial
      grind

lemma exprWitness_sound {locs : List Loc} {ℓ : NFact locs} {σ : State} {expr : Expr} {n : Int}
    (hcorr : ncorr ℓ σ)
    (heval : EvalExpr σ expr (Val.Int n))
    (htruthy : n ≠ 0) :
    ncorr_self (fun i => (
      if exprWitness locs ℓ expr i = NVal.nonnull then NVal.nonnull else (ℓ i).fst,
      (ℓ i).snd
    )) σ := by
  intro i v h henv rfl
  apply hcorr.left <;> try trivial
  simp! [exprWitness] at h
  apply h
  intro hass
  absurd hass
  apply nonNullAssumption_sound <;> trivial

private lemma n_preserve_update_none (ℓ : NFact locs)
    (hnone : locs.finIdxOf? x = none) (hcorr : ncorr ℓ σ) :
    ncorr ℓ (σ.updated x v) := by
  simp only [ncorr, ncorr_self, ncorr_wit, State.updated] at *
  grind [List.finIdxOf?_eq_none_iff]

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
      simp [ncorr, ncorr_self, ncorr_wit, State.empty]
    preserve_step := by
      intro e σ σ' ℓ hstep hcorr
      simp only [nDFA_transferAlong, nTransfer, CFG.nodeKind]
      cases hstep with simp only [*]
      | assign _ heval _ =>
        rename_i x expr v _ _
        split
        · apply n_preserve_update_none <;> trivial
        · rename_i i hi
          split_ands
          · intro j v' h hupd rfl
            simp only at h
            split_ifs at h
            · subst j
              have hget := List.finIdxOf?_eq_some_iff.mp hi |>.left
              rw [Fin.getElem_fin] at hget
              rw [List.get_eq_getElem, hget, State.updated_eq σ x v] at hupd
              have h_v_not_null : v ≠ Val.Null := evalExpr_sound hcorr.left heval h
              grind
            · have h_x_neq : x ≠ locs.get j := by apply List.finIdxOf?_nodup <;> trivial
              rw [State.updated_neq] at hupd <;> try trivial
              apply hcorr.left <;> trivial
          · intro j k n v' hupd1 habs hn hupd2 rfl
            simp only at hupd1
            split_ifs at hupd1 <;> simp only at hupd1
            · subst j
              have hget := List.finIdxOf?_eq_some_iff.mp hi |>.left
              rw [Fin.getElem_fin] at hget
              rw [List.get_eq_getElem, hget, State.updated_eq σ x v] at habs
              injection habs
              subst v
              by_cases h_ki : k = i
              · subst k
                rw [List.get_eq_getElem, hget, State.updated_eq] at hupd2
                injection hupd2
                contradiction
              · have h_x_neq : x ≠ locs.get k := by apply List.finIdxOf?_nodup <;> trivial
                rw [State.updated_neq] at hupd2 <;> try trivial
                apply exprWitness_sound hcorr heval hn k .Null <;> grind
            · have h_x_neq : x ≠ locs.get j := by apply List.finIdxOf?_nodup <;> trivial
              rw [State.updated_neq] at habs <;> try trivial
      | @assum _ _ n _ _ _ heval htruthy _ =>
        have : n ≠ 0 := by grind
        simp only [ncorr, beq_iff_eq]
        split_ands
        · apply exprWitness_sound <;> trivial
        · apply hcorr.right
    preserve_stutter := by
      intro _n σ σ' ℓ hstut hcorr
      simp only [LangSem.LStutter] at hstut
      subst hstut
      assumption
  }

theorem mono_absorb_corr_self
    {ℓ ℓ' : NFact locs} {σ : State} (h : ℓ ⊑ ℓ')
    (hcorr : ncorr_self ℓ σ) : ncorr_self ℓ' σ := by
  simp only [ncorr_self] at *
  intros i v habs
  have hi : (ℓ i).fst ⊑ (ℓ' i).fst := by
    exact congrArg (fun ρ => (ρ i).fst) h
  rw [habs] at hi
  simp only [max] at hi
  generalize heq : ℓ i = x at hi
  grind
theorem mono_absorb_corr_wit
    {ℓ ℓ' : NFact locs} {σ : State} (h : ℓ ⊑ ℓ')
    (hcorr : ncorr_wit ℓ σ) : ncorr_wit ℓ' σ := by
  simp only [ncorr_wit] at *
  intro i j n v habs
  have hi : (ℓ i).snd ⊑ (ℓ' i).snd := by
    exact congrArg (fun ρ => (ρ i).snd) h
  apply Domain.ord_distr at hi
  rw [habs] at hi
  simp only [max] at hi
  generalize heq : (ℓ i).snd j = x at hi
  cases x <;> grind
theorem mono_absorb_corr
    {ℓ ℓ' : NFact locs} {σ : State} (h : ℓ ⊑ ℓ')
    (hcorr : ncorr ℓ σ) : ncorr ℓ' σ := by
  unfold ncorr at *
  grind [mono_absorb_corr_self, mono_absorb_corr_wit]


/-! ## Bundled Nullability analysis -/

/-- A bundled `Flow.Analysis` for nullability, parameterized by
    the variable list, a `Nodup` proof, and the underlying CFG. -/
@[reducible]
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

/-- Wrapper around `Flow.analyze`: run the bundled Nullability
    analysis directly on a `CFG`. -/
def nAnalyzeCFG {locs : List Loc} (hnd : locs.Nodup)
    (cfg : WFCFG) :
    Flow.AnalysisResult (nAnalysis hnd cfg) :=
  Flow.analyze (nAnalysis hnd cfg)

/-- Turn-key correctness for the bundled nullability analysis: at every reachable
    program point, the computed in fact correctly approximates the
    concrete state. -/
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

def checkExpr {locs : List Loc} (ℓ : NFact locs) : Expr -> Bool
  | .Null => true
  | .Int _ => true
  | .Var _ => true
  | .IsNull e => checkExpr ℓ e
  | .Not e =>
      checkExpr ℓ e && (evalExpr locs ℓ e == NVal.nonnull)
  | .BinOp _ e₁ e₂ =>
      checkExpr ℓ e₁ && checkExpr ℓ e₂ &&
      (evalExpr locs ℓ e₁ == NVal.nonnull) && (evalExpr locs ℓ e₂ == NVal.nonnull)

def checkNode {locs : List Loc} (ℓ : NFact locs) : NodeKind -> Bool
  | .Skip => true
  | .Assign _ e => checkExpr ℓ e
  | .Assume e => checkExpr ℓ e

def checkCFG (cfg : WFCFG) : Bool :=
  let locs := vars cfg
  let res := (nAnalyzeCFG locs.prop cfg).inFacts
  (List.range cfg.val.nodes.length).all fun n =>
    match cfg.val.nodes[n]? with
    | none => false
    | some kind => checkNode (res n) kind

end Duke.Analysis.Nullability

import Chartreux.Analysis.Generic
import Chartreux.Analysis.Worklist
import Chartreux.Analysis.WorklistProofs
import Chartreux.Duke.Eval
import Chartreux.Duke.CFG
import Chartreux.Duke.Utils
import Mathlib.Tactic.Common

namespace Duke.Analysis.Nullability

open Chartreux.Analysis
open Chartreux.Analysis.Generic

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

instance : SemiLattice NVal where
  join_comm  := by intro a b; cases a <;> cases b <;> rfl
  join_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  join_idem  := by intro a; cases a <;> rfl

instance : Bounded NVal where
  bot_le     := by intro a; cases a <;> rfl

/-! ## CFG transition functions -/

/-- Nullability consequent for other variables -/
abbrev Consequent (locs : Nat) : Type := Domain locs NVal
def emptyConsequent (locs : Nat) : Consequent locs := fun _ => .top

/-- A nullability fact for a program with location `locs`
    is a `Domain` over
    * `NVal` - am I nonnull?
    * `Consequent` - do I witness that others are nonnull?
-/
abbrev Fact (locs : Nat) : Type := Domain locs (NVal × Consequent locs)

def extractConsequents (locs : Nat) (cons : Consequent locs) : List Nat :=
  (List.finRange locs).filterMap (
    fun i => match cons i with
             | .nonnull => some i
             | _ => none
  )

def formatConsequents (mapping : Mapping) (consequents : List Nat) : String :=
  "{" ++ String.intercalate ", " (consequents.map mapping.get) ++ "}"

/-- Pretty-print a nullability fact using variable names. For each tracked
    variable we show its abstract nullability value and the set of variables
    it witnesses as nonnull. -/
def formatFact (mapping : Mapping) (locs : Nat) (ℓ : Fact locs) : String :=
  let parts : List String :=
    (List.finRange locs).map fun i =>
      let (v, cons) := ℓ i
      let conss := extractConsequents locs cons
      s!"{mapping.get i}={v}" ++
        if conss.isEmpty then "" else s!" ⇒ {formatConsequents mapping conss}"
  "[" ++ String.intercalate ", " parts ++ "]"

def nonNullAssumption (locs : Nat) (ℓ : Fact locs) (e : NExpr) : List Nat :=
  match e with
  | .BinOp .and e₁ e₂ => nonNullAssumption locs ℓ e₁ ++ nonNullAssumption locs ℓ e₂
  | .Not (.IsNull (.Var x)) => [x]
  | .Var x =>
      if h : x < locs then
        ℓ (Fin.mk x h) |>.snd |> extractConsequents locs
      else
        []
  | _ => []

/-- What is the consequent of this expression being true? -/
def exprConsequent (locs : Nat) (ℓ : Fact locs) (e : NExpr) : Consequent locs :=
  let nonNull := nonNullAssumption locs ℓ e
  fun j => if nonNull.contains j then .nonnull else .top

def evalExpr (locs : Nat) (ℓ : Fact locs) : NExpr → NVal
  | .Null => .top
  | .Int _ => .nonnull
  | .Var x =>
      if h : x < locs then
        ℓ (Fin.mk x h) |>.fst
      else
        .top
  | .IsNull _ => .nonnull
  | .Not _ => .nonnull
  | .BinOp _ e₁ e₂ => evalExpr locs ℓ e₁ ⊔ evalExpr locs ℓ e₂

def nodeTransfer (locs : Nat) (g : CFG) (n : NodeID) :
    Fact locs -> Fact locs := fun ρ =>
  match g.nodeKind n with
  | some (.Declare l (some e)) | some (.Assign l e) =>
    let v := evalExpr locs ρ e
    let cons := exprConsequent locs ρ e
    -- mutation might have invalidated some of the implications
    -- we could be smart about just invalidating relevant ones,
    -- but for now we just invalidate all of them.
    -- TODO: invalidate only relevant bits
    fun j => if j = l then (v, cons) else (ρ j |>.fst, emptyConsequent locs)
  | some (.Declare l none) =>
    fun j => (if j = l then .top else ρ j |>.fst, emptyConsequent locs)
  | some (.Assume e) =>
    let cons := exprConsequent locs ρ e
    -- we preserve the implications from before, but update the nullability status
    fun i => (if cons i == .nonnull then .nonnull else ρ i |>.fst, ρ i |>.snd)
  | some .Skip | some .BlockEnter | some .BlockExit | none => ρ

/-- Edge transfer for forward nullability is the identity. -/
def edgeTransfer (locs : Nat) : Edge -> Fact locs -> Fact locs :=
  fun _ a => a

/-- The default initial fact: every tracked variable is `nonnull` and witnesses nothing. -/
def entryInit (locs : Nat) : Fact locs := fun _ => (.nonnull, emptyConsequent locs)

/-! ### Transfer function monotonicity
    Technically not needed. But it being true implies that the result is the least post-fixpoint
-/

variable (cfg : WFCFG)
variable {locs : Nat}

private lemma extractConsequents_incl (ρ₁ ρ₂ : Consequent locs)
    (hρ : ρ₁ ⊑ ρ₂) (l : Nat) :
    l ∈ extractConsequents locs ρ₂ -> l ∈ extractConsequents locs ρ₁ := by
  unfold extractConsequents
  intro h
  rw [List.mem_filterMap] at *
  have ⟨i, hin, heq⟩ := h
  use i
  apply Domain.ord_distr (i := i) at hρ
  generalize h1 : ρ₁ i = x₁ at *
  generalize h2 : ρ₂ i = x₂ at *
  cases x₁ <;> cases x₂ <;> trivial

private lemma nonNullAssumption_incl (ℓ₁ ℓ₂ : Fact locs)
    (hρ : ℓ₁ ⊑ ℓ₂) (e : NExpr) (l : Nat) :
    l ∈ nonNullAssumption locs ℓ₂ e -> l ∈ nonNullAssumption locs ℓ₁ e := by
  induction e generalizing l with try grind [nonNullAssumption]
  | Not e =>
    unfold nonNullAssumption at *
    cases e <;> try simp
    rename_i e h
    cases e <;> simp
  | BinOp op e₁ e₂ ih₁ ih₂ =>
    intro hin
    cases op <;> grind [nonNullAssumption]
  | Var x =>
    simp! [nonNullAssumption]
    intro hx y
    refine Exists.intro hx ?_
    apply extractConsequents_incl <;> try trivial
    exact congrArg (fun ℓ => (ℓ ⟨x, hx⟩).snd) hρ

private lemma exprConsequent_mono (ℓ₁ ℓ₂ : Fact locs)
    (hρ : ℓ₁ ⊑ ℓ₂) (e : NExpr) :
    exprConsequent locs ℓ₁ e ⊑ exprConsequent locs ℓ₂ e := by
  unfold exprConsequent
  simp only
  funext j
  rw [Domain.max_app]
  repeat split <;> try rfl
  grind [nonNullAssumption_incl]

private lemma evalExpr_mono (ℓ₁ ℓ₂ : Fact locs)
    (hρ : ℓ₁ ⊑ ℓ₂) (e : NExpr) :
    evalExpr locs ℓ₁ e ⊑ evalExpr locs ℓ₂ e := by
  induction e with (simp only [evalExpr]; try grind [SemiLattice.join_idem])
  | Var x =>
    split <;> try rfl
    rename_i h
    exact congrArg (fun ℓ => (ℓ ⟨x, h⟩).fst) hρ
  | BinOp op e₁ e₂ ih₁ ih₂ =>
    cases ha₁ : evalExpr locs ℓ₁ e₁ <;>
      cases hb₁ : evalExpr locs ℓ₁ e₂ <;>
      cases ha₂ : evalExpr locs ℓ₂ e₁ <;>
      cases hb₂ : evalExpr locs ℓ₂ e₂ <;>
      rw [ha₁, ha₂] at ih₁ <;>
      rw [hb₁, hb₂] at ih₂ <;>
      simp_all [Max.max]

private lemma nodeTransfer_mono (n : NodeID) :
    mono_f (nodeTransfer locs cfg n) := by
  intro ℓ₁ ℓ₂ hxy
  funext j
  change (nodeTransfer locs cfg n ℓ₁) j ⊑ (nodeTransfer locs cfg n ℓ₂) j
  unfold nodeTransfer
  simp only
  generalize hk : cfg.val.nodeKind n = nk
  cases nk with
  | none => apply Domain.ord_distr; assumption
  | some k =>
    cases k with (try simp only; try grind [Domain.ord_distr hxy])
    | Declare x e =>
      cases e with simp only
      | none =>
        split <;> try rfl
        ext
        case fst => exact congrArg (fun ℓ => (ℓ j).fst) hxy
        case h k => rfl
      | some e =>
        split
        · ext
          case fst => apply evalExpr_mono; assumption
          case h k => apply Domain.ord_distr; apply exprConsequent_mono; assumption
        · ext
          case fst => exact congrArg (fun ℓ => (ℓ j).fst) hxy
          case h k => rfl
    | Assign x e =>
      split
      · ext
        case fst =>
          apply evalExpr_mono
          assumption
        case h k =>
          apply Domain.ord_distr
          apply exprConsequent_mono
          assumption
      · ext
        case fst => exact congrArg (fun ℓ => (ℓ j).fst) hxy
        case h k => rfl
    | Assume e =>
      ext
      case fst =>
        have hw_mono := Domain.ord_distr (exprConsequent_mono ℓ₁ ℓ₂ hxy e) (i := j)
        generalize hw1 : exprConsequent locs ℓ₁ e j = w₁ at *
        generalize hw2 : exprConsequent locs ℓ₂ e j = w₂ at *
        cases w₁ <;> cases w₂ <;> simp [Max.max] at * <;> grind
      case h i =>
        apply Domain.ord_distr
        exact congrArg (fun ℓ => (ℓ j).snd) hxy

private lemma edgeTransfer_mono :
    ∀ e, mono_f (edgeTransfer locs e) := fun _ _ _ h => h

/-! ## Coherence predicate for concrete and abstract states -/

/-- For each variable, if the analysis tells us it is not null, the concrete value is not null -/
def coh_self (ℓ : Fact locs) (σ : NState) : Prop :=
  ∀ i v,
    (ℓ i).fst = .nonnull ->
    σ i = .declared (some v) ->
    v ≠ .Null
/-- Variable `i` is the witness that variable `j` is not null -/
def coh_impl (ℓ : Fact locs) (σ : NState) : Prop :=
  ∀ i j n v,
    (ℓ i).snd j = .nonnull ->
    σ i = .declared (some (.Int n)) ->
    n ≠ 0 -> -- if variable `i` is truthy
    σ j = .declared (some v) ->
    v ≠ .Null

def coh (ℓ : Fact locs) (σ : NState) : Prop := coh_self ℓ σ ∧ coh_impl ℓ σ

/-- The DFA closure for nullability, parameterised by the underlying CFG.
    The CFG is needed to read `nodeKind`. -/
@[reducible]
def DFA (locs : Nat) : DFA NodeID Edge where
  L            := Fact locs
  nodeTransfer := nodeTransfer locs cfg
  edgeTransfer := edgeTransfer locs
  entry        := entryInit locs

lemma evalExpr_sound {locs : Nat} {ℓ : Fact locs} {σ : NState} {expr : NExpr} {v : Val}
    (hcoh : coh_self ℓ σ)
    (heval : EvalExpr σ expr v)
    (h_abs : evalExpr locs ℓ expr = NVal.nonnull) : v ≠ Val.Null := by
  induction heval with simp! [evalExpr] at *
  | @var x v h =>
    split at h_abs <;> try contradiction
    rename_i hi
    apply hcoh <;> try trivial

lemma nonNullAssumption_sound {locs : Nat} {ℓ : Fact locs} {σ : NState} {expr : NExpr} {n : Int}
    {i : Nat}
    (hcoh : coh ℓ σ)
    (heval : EvalExpr σ expr (Val.Int n))
    (htruthy : n ≠ 0)
    (hget : σ i = .declared (some Val.Null)) :
    i ∉ nonNullAssumption locs ℓ expr := by
  induction expr generalizing n with (intro hass; try simp! [nonNullAssumption] at hass)
  | Not e =>
    cases e with try simp! [nonNullAssumption] at hass
    | IsNull e' =>
      cases e' with try simp! [nonNullAssumption] at hass
      | Var x =>
        subst_vars
        cases heval with try trivial
        | notF _ heval_not =>
          cases heval_not with
          | isnullF _ v heval_var hneq_null =>
            cases heval_var with
            | var _ _ h_sig =>
              rw [h_sig] at hget
              injection hget with hget
              injection hget
              contradiction
  | BinOp op e₁ e₂ ih₁ ih₂ =>
    cases op with simp! [nonNullAssumption] at hass
    | and =>
      cases heval with
      | binop _ _ _ n₁ n₂ eval₁ eval₂ =>
        have h1_neq : n₁ ≠ 0 := by grind [applyOp]
        have h2_neq : n₂ ≠ 0 := by grind [applyOp]
        grind
  | Var x =>
    simp! [nonNullAssumption, extractConsequents] at hass
    rcases hass with ⟨hx, a, h_eq⟩
    split at h_eq <;> try trivial
    injection h_eq
    subst_vars
    cases heval with
    | var _ _ h_sig =>
      apply hcoh.right <;> trivial

lemma exprConsequent_sound {locs : Nat} {ℓ : Fact locs} {σ : NState} {expr : NExpr} {n : Int}
    (hcoh : coh ℓ σ)
    (heval : EvalExpr σ expr (Val.Int n))
    (htruthy : n ≠ 0) :
    coh_self (fun i => (
      if exprConsequent locs ℓ expr i = NVal.nonnull then NVal.nonnull else (ℓ i).fst,
      (ℓ i).snd
    )) σ := by
  intro i v h henv rfl
  apply hcoh.left <;> try trivial
  simp! [exprConsequent] at h
  apply h
  intro hass
  absurd hass
  apply nonNullAssumption_sound <;> trivial

@[simp] private lemma DFA_transferAlong (cfg : WFCFG)
    (e : EdgeOf cfg.analysis) (ℓ : Fact locs) :
    (DFA cfg locs).transferAlong cfg.analysis e ℓ =
    nodeTransfer locs cfg e.val.src ℓ := rfl

/-- The nullability `DFASemantics` for a fixed CFG. The three preservation
    fields directly consume the abstract `LangSem` transitions. -/
def semantics :
    DFASemantics (ls := dukeLangSem cfg) cfg.analysis (DFA cfg locs) :=
  { Coh := coh
    preserve_entry := by
      intro σ hinit
      cases hinit
      simp [coh, coh_self, coh_impl, State.empty]
    preserve_step := by
      intro e σ σ' ℓ hstep hcoh
      simp only [DFA_transferAlong, nodeTransfer]
      cases hstep with simp only [*]
      | @declare _ _ x _ _ _ _ hdecl =>
        split_ands
        · intro j v' h hget rfl
          simp only at h
          split_ifs at h
          rw [State.declared_neq (by grind) hdecl] at hget
          apply hcoh.left <;> trivial
        · intro j k n v' habs hdecl1 hn hdecl2 rfl
          contradiction
      | @declareVal _ _ x expr v _ _ _ _ heval _ hdecl hupd =>
        split_ands
        · intro j v' h hget rfl
          simp only at h
          split_ifs at h <;> simp only at h
          · subst x
            rw [State.updated_eq hupd] at hget
            have h_v_not_null : v ≠ Val.Null := evalExpr_sound hcoh.left heval h
            grind
          · rw [State.updated_neq (by grind) hupd] at hget
            rw [State.declared_neq (by grind) hdecl] at hget
            apply hcoh.left <;> trivial
        · intro j k n v' hupd1 habs hn hupd2 rfl
          simp only at hupd1
          split_ifs at hupd1 <;> simp only at hupd1
          · subst x
            rw [State.updated_eq hupd] at habs
            injection habs with habs
            injection habs
            subst v
            by_cases h_ki : k = j
            · subst k
              rw [State.updated_eq hupd] at hupd2
              injection hupd2 with hupd2
              injection hupd2
              contradiction
            · rw [State.updated_neq (by grind) hupd] at hupd2
              rw [State.declared_neq (by grind) hdecl] at hupd2
              apply exprConsequent_sound hcoh heval hn k .Null <;> grind
          · contradiction
      | @assign _ _ x expr v _ _ _ heval _ hupd =>
        split_ands
        · intro j v' h hget rfl
          simp only at h
          split_ifs at h <;> simp only at h
          · subst x
            rw [State.updated_eq hupd] at hget
            have h_v_not_null : v ≠ Val.Null := evalExpr_sound hcoh.left heval h
            grind
          · rw [State.updated_neq (by grind) hupd] at hget
            apply hcoh.left <;> trivial
        · intro j k n v' hupd1 habs hn hupd2 rfl
          simp only at hupd1
          split_ifs at hupd1 <;> simp only at hupd1
          · subst x
            rw [State.updated_eq hupd] at habs
            injection habs with habs
            injection habs
            subst v
            by_cases h_ki : k = j
            · subst k
              rw [State.updated_eq hupd] at hupd2
              injection hupd2 with hupd2
              injection hupd2
              contradiction
            · rw [State.updated_neq (by grind) hupd] at hupd2
              apply exprConsequent_sound hcoh heval hn k .Null <;> grind
          · contradiction
      | @assum _ _ n _ _ _ heval htruthy _ =>
        have : n ≠ 0 := by grind
        simp only [beq_iff_eq]
        split_ands
        · apply exprConsequent_sound <;> trivial
        · apply hcoh.right
    preserve_stutter := by
      intro _n σ σ' ℓ hstut hcoh
      simp only [LangSem.LStutter] at hstut
      subst hstut
      assumption
  }

theorem mono_absorb_coh_self
    {ℓ ℓ' : Fact locs} {σ : NState} (h : ℓ ⊑ ℓ')
    (hcoh : coh_self ℓ σ) : coh_self ℓ' σ := by
  simp only [coh_self] at *
  intros i v habs
  have hi : (ℓ i).fst ⊑ (ℓ' i).fst := by
    exact congrArg (fun ρ => (ρ i).fst) h
  rw [habs] at hi
  simp only [max] at hi
  generalize heq : ℓ i = x at hi
  grind
theorem mono_absorb_coh_impl
    {ℓ ℓ' : Fact locs} {σ : NState} (h : ℓ ⊑ ℓ')
    (hcoh : coh_impl ℓ σ) : coh_impl ℓ' σ := by
  simp only [coh_impl] at *
  intro i j n v habs
  have hi : (ℓ i).snd ⊑ (ℓ' i).snd := by
    exact congrArg (fun ρ => (ρ i).snd) h
  apply Domain.ord_distr at hi
  rw [habs] at hi
  simp only [max] at hi
  generalize heq : (ℓ i).snd j = x at hi
  cases x <;> grind
theorem mono_absorb_coh
    {ℓ ℓ' : Fact locs} {σ : NState} (h : ℓ ⊑ ℓ')
    (hcoh : coh ℓ σ) : coh ℓ' σ := by
  unfold coh at *
  grind [mono_absorb_coh_self, mono_absorb_coh_impl]


/-! ## Bundled Nullability analysis -/

/-- A bundled `Chartreux.Analysis` for nullability, parameterized by
    the variable list, a `Nodup` proof, and the underlying CFG. -/
@[reducible]
def analysis {locs : Nat} (cfg : WFCFG) :
    Chartreux.Analysis (ls := dukeLangSem cfg) NodeID Edge State :=
  { dfa          := DFA cfg locs
    botL         := (inferInstance : Bot (Fact locs))
    maxL         := _
    decEqL       := (inferInstance : DecidableEq (Fact locs))
    fhL          := (inferInstance : FiniteHeight (Fact locs))
    llL          := (inferInstance : SemiLattice (Fact locs))
    semantics    := semantics cfg
    mono_absorb  := mono_absorb_coh
    edge_mono    := edgeTransfer_mono }

/-- Wrapper around `Chartreux.analyze`: run the bundled Nullability
    analysis directly on a `CFG`. -/
def analyzeCFG {locs : Nat} (cfg : WFCFG) :
    Chartreux.AnalysisResult (@analysis locs cfg) :=
  Chartreux.analyze (analysis cfg)

/-- Turn-key correctness for the bundled nullability analysis: at every reachable
    program point, the computed in fact correctly approximates the
    concrete state. -/
theorem reachable_correct
    {locs : Nat} (cfg : WFCFG) :
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

def checkExpr {locs : Nat} (ℓ : Fact locs) : NExpr -> Bool
  | .Null => true
  | .Int _ => true
  | .Var _ => true
  | .IsNull e => checkExpr ℓ e
  | .Not e =>
      checkExpr ℓ e && (evalExpr locs ℓ e == NVal.nonnull)
  | .BinOp _ e₁ e₂ =>
      checkExpr ℓ e₁ && checkExpr ℓ e₂ &&
      (evalExpr locs ℓ e₁ == NVal.nonnull) && (evalExpr locs ℓ e₂ == NVal.nonnull)

def checkNode {locs : Nat} (ℓ : Fact locs) : NodeKind -> Bool
  | .Skip | .BlockEnter | .BlockExit | .Declare _ none => true
  | .Declare _ (some e) | .Assign _ e => checkExpr ℓ e
  | .Assume e => checkExpr ℓ e && (evalExpr locs ℓ e == NVal.nonnull)

def checkCFG (cfg : WFCFG) : Bool :=
  let locs := totalVars cfg
  let res := (@analyzeCFG locs cfg).inFacts
  (List.range cfg.val.nodes.length).all fun n =>
    match cfg.val.nodeKind n with
    | none => false
    | some kind => checkNode (res n) kind

end Duke.Analysis.Nullability

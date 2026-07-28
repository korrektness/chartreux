import Chartreux.Analysis.Generic
import Chartreux.Analysis.Worklist
import Chartreux.Analysis.WorklistProofs
import Chartreux.Duke.Eval
import Chartreux.Duke.CFG
import Chartreux.Duke.Utils
import Mathlib.Data.List.Nodup

namespace Duke.Analysis.Nullability

abbrev Loc := String

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
abbrev Consequent (locs : List Loc) : Type := Domain locs.length NVal
def emptyConsequent (locs : List Loc) : Consequent locs := fun _ => .top

/-- A nullability fact for a program with location `locs`
    is a `Domain` over
    * `NVal` - am I nonnull?
    * `Consequent` - do I witness that others are nonnull?
-/
abbrev Fact (locs : List Loc) : Type := Domain locs.length (NVal × Consequent locs)

def extractConsequents (locs : List Loc) (cons : Consequent locs) : List Loc :=
  (List.finRange locs.length).filterMap (
    fun i => match cons i with
             | .nonnull => some (locs.get i)
             | _ => none
  )

def formatConsequents (consequents : List Loc) : String :=
  "{" ++ String.intercalate ", " consequents ++ "}"

/-- Pretty-print a nullability fact using variable names. For each tracked
    variable we show its abstract nullability value and the set of variables
    it witnesses as nonnull. -/
def formatFact (locs : List Loc) (ℓ : Fact locs) : String :=
  let parts : List String :=
    (List.finRange locs.length).map fun i =>
      let (v, cons) := ℓ i
      let conss := extractConsequents locs cons
      s!"{locs.get i}={v}" ++ if conss.isEmpty then "" else s!" ⇒ {formatConsequents conss}"
  "[" ++ String.intercalate ", " parts ++ "]"

def nonNullAssumption (locs : List Loc) (ℓ : Fact locs) (e : Expr) : List Loc :=
  match e with
  | .BinOp .and e₁ e₂ => nonNullAssumption locs ℓ e₁ ++ nonNullAssumption locs ℓ e₂
  | .Not (.IsNull (.Var x)) => [x]
  | .Var x =>
      match locs.finIdxOf? x with
      | none   => []
      | some i => ℓ i |>.snd |> extractConsequents locs
  | _ => []

/-- What is the consequent of this expression being true? -/
def exprConsequent (locs : List Loc) (ℓ : Fact locs) (e : Expr) : Consequent locs :=
  let nonNull := nonNullAssumption locs ℓ e |>.filterMap locs.finIdxOf?
  fun j => if nonNull.contains j then .nonnull else .top

def evalExpr (locs : List Loc) (ℓ : Fact locs) : Expr → NVal
  | .Null => .top
  | .Int _ => .nonnull
  | .Var x =>
      match locs.finIdxOf? x with
      | none   => .top
      | some i => ℓ i |>.fst
  | .IsNull _ => .nonnull
  | .Not _ => .nonnull
  | .BinOp _ e₁ e₂ => evalExpr locs ℓ e₁ ⊔ evalExpr locs ℓ e₂

def nodeTransfer (locs : List Loc) (g : CFG) (n : NodeID) :
    Fact locs -> Fact locs := fun ρ =>
  match g.nodeKind n with
  | some (.Assign l e) =>
    match locs.finIdxOf? l with
    | none   => ρ
    | some i =>
        let v := evalExpr locs ρ e
        let cons := exprConsequent locs ρ e
        -- mutation might have invalidated some of the implications
        -- we could be smart about just invalidating relevant ones,
        -- but for now we just invalidate all of them.
        -- TODO: invalidate only relevant bits
        fun j => if j = i then (v, cons) else (ρ j |>.fst, emptyConsequent locs)
  | some (.Assume e) =>
    let cons := exprConsequent locs ρ e
    -- we preserve the implications from before, but update the nullability status
    fun i => (if cons i == .nonnull then .nonnull else ρ i |>.fst, ρ i |>.snd)
  | some .Skip | none => ρ

/-- Edge transfer for forward nullability is the identity. -/
def edgeTransfer (vars : List String) : Edge -> Fact vars -> Fact vars :=
  fun _ a => a

/-- The default initial fact: every tracked variable is `nonnull` and witnesses nothing. -/
def entryInit (locs : List Loc) : Fact locs := fun _ => (.nonnull, emptyConsequent locs)

/-! ### Transfer function monotonicity
    Technically not needed. But it being true implies that the result is the least post-fixpoint
-/

variable (cfg : WFCFG)
variable {locs : List Loc}

private lemma extractConsequents_incl (ρ₁ ρ₂ : Consequent locs)
    (hρ : ρ₁ ⊑ ρ₂) (l : Loc) :
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
    (hρ : ℓ₁ ⊑ ℓ₂) (e : Expr) (l : Loc) :
    l ∈ nonNullAssumption locs ℓ₂ e -> l ∈ nonNullAssumption locs ℓ₁ e := by
  induction e generalizing l with try grind [nonNullAssumption]
  | Not e => unfold nonNullAssumption at *; grind
  | BinOp op e₁ e₂ ih₁ ih₂ =>
    intro hin
    cases op <;> grind [nonNullAssumption]
  | Var x =>
    simp [nonNullAssumption]
    split <;> try grind
    rename_i i _
    apply extractConsequents_incl
    exact congrArg (fun ℓ => (ℓ i).snd) hρ

private lemma exprConsequent_mono (ℓ₁ ℓ₂ : Fact locs)
    (hρ : ℓ₁ ⊑ ℓ₂) (e : Expr) :
    exprConsequent locs ℓ₁ e ⊑ exprConsequent locs ℓ₂ e := by
  unfold exprConsequent
  simp only
  funext j
  rw [Domain.max_app]
  repeat split <;> try rfl
  rename_i hneg hpos
  absurd hneg
  rw [List.contains_iff_mem, List.mem_filterMap] at *
  grind [nonNullAssumption_incl]

private lemma evalExpr_mono (ℓ₁ ℓ₂ : Fact locs)
    (hρ : ℓ₁ ⊑ ℓ₂) (e : Expr) :
    evalExpr locs ℓ₁ e ⊑ evalExpr locs ℓ₂ e := by
  induction e with (simp only [evalExpr]; try grind [SemiLattice.join_idem])
  | Var x =>
    split <;> try rfl
    rename_i i _
    exact congrArg (fun ℓ => (ℓ i).fst) hρ
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
def coh_self (ℓ : Fact locs) (σ : State) : Prop :=
  ∀ i v,
    (ℓ i).fst = .nonnull ->
    σ (locs.get i) = some v ->
    v ≠ .Null
/-- Variable `i` is the witness that variable `j` is not null -/
def coh_impl (ℓ : Fact locs) (σ : State) : Prop :=
  ∀ i j n v,
    (ℓ i).snd j = .nonnull ->
    σ (locs.get i) = some (.Int n) ->
    n ≠ 0 -> -- if variable `i` is truthy
    σ (locs.get j) = some v ->
    v ≠ .Null

def coh (ℓ : Fact locs) (σ : State) : Prop := coh_self ℓ σ ∧ coh_impl ℓ σ

/-- The DFA closure for nullability, parameterised by the underlying CFG.
    The CFG is needed to read `nodeKind`. -/
@[reducible]
def DFA (locs : List Loc) : DFA NodeID Edge where
  L            := Fact locs
  nodeTransfer := nodeTransfer locs cfg
  edgeTransfer := edgeTransfer locs
  entry        := entryInit locs

lemma evalExpr_sound {locs : List Loc} {ℓ : Fact locs} {σ : State} {expr : Expr} {v : Val}
    (hcoh : coh_self ℓ σ)
    (heval : EvalExpr σ expr v)
    (h_abs : evalExpr locs ℓ expr = NVal.nonnull) : v ≠ Val.Null := by
  induction heval with simp! [evalExpr] at *
  | @var x v h =>
    split at h_abs <;> try contradiction
    rename_i hi
    apply hcoh <;> try trivial
    grind [List.finIdxOf?_eq_some_iff]

lemma nonNullAssumption_sound {locs : List Loc} {ℓ : Fact locs} {σ : State} {expr : Expr} {n : Int}
    {i : Fin locs.length}
    (hcoh : coh ℓ σ)
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
    simp! [nonNullAssumption, extractConsequents] at hass
    split at hass <;> try trivial
    rename_i j hin
    have ⟨rfl, _⟩ := List.finIdxOf?_eq_some_iff.mp hin
    cases heval with
    | var _ _ h_sig =>
      simp only [List.mem_filterMap, List.mem_finRange, true_and] at hass
      obtain ⟨a, ha⟩ := hass
      cases h_snd : (ℓ j).snd a <;> simp [h_snd] at ha
      apply hcoh.right <;> try trivial
      grind

lemma exprConsequent_sound {locs : List Loc} {ℓ : Fact locs} {σ : State} {expr : Expr} {n : Int}
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

private lemma preserve_update_none (ℓ : Fact locs)
    (hnone : locs.finIdxOf? x = none) (hcoh : coh ℓ σ) :
    coh ℓ (σ.updated x v) := by
  simp only [coh, coh_self, coh_impl, State.updated] at *
  grind [List.finIdxOf?_eq_none_iff]

@[simp] private lemma DFA_transferAlong (cfg : WFCFG)
    (e : EdgeOf cfg.analysis) (ℓ : Fact locs) :
    (DFA cfg locs).transferAlong cfg.analysis e ℓ =
    nodeTransfer locs cfg e.val.src ℓ := rfl

/-- The nullability `DFASemantics` for a fixed CFG. The three preservation
    fields directly consume the abstract `LangSem` transitions. -/
def semantics (hnd : locs.Nodup) :
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
      | assign _ heval _ =>
        rename_i x expr v _ _
        split
        · apply preserve_update_none <;> trivial
        · rename_i i hi
          split_ands
          · intro j v' h hupd rfl
            simp only at h
            split_ifs at h
            · subst j
              have hget := List.finIdxOf?_eq_some_iff.mp hi |>.left
              rw [Fin.getElem_fin] at hget
              rw [List.get_eq_getElem, hget, State.updated_eq σ x v] at hupd
              have h_v_not_null : v ≠ Val.Null := evalExpr_sound hcoh.left heval h
              grind
            · have h_x_neq : x ≠ locs.get j := by apply List.finIdxOf?_nodup <;> trivial
              rw [State.updated_neq] at hupd <;> try trivial
              apply hcoh.left <;> trivial
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
                apply exprConsequent_sound hcoh heval hn k .Null <;> grind
            · have h_x_neq : x ≠ locs.get j := by apply List.finIdxOf?_nodup <;> trivial
              rw [State.updated_neq] at habs <;> try trivial
      | @assum _ _ n _ _ _ heval htruthy _ =>
        have : n ≠ 0 := by grind
        simp only [coh, beq_iff_eq]
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
    {ℓ ℓ' : Fact locs} {σ : State} (h : ℓ ⊑ ℓ')
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
    {ℓ ℓ' : Fact locs} {σ : State} (h : ℓ ⊑ ℓ')
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
    {ℓ ℓ' : Fact locs} {σ : State} (h : ℓ ⊑ ℓ')
    (hcoh : coh ℓ σ) : coh ℓ' σ := by
  unfold coh at *
  grind [mono_absorb_coh_self, mono_absorb_coh_impl]


/-! ## Bundled Nullability analysis -/

/-- A bundled `Chartreux.Analysis` for nullability, parameterized by
    the variable list, a `Nodup` proof, and the underlying CFG. -/
@[reducible]
def analysis {locs : List Loc} (hnd : locs.Nodup) (cfg : WFCFG) :
    Chartreux.Analysis (ls := dukeLangSem cfg) NodeID Edge State :=
  { dfa          := DFA cfg locs
    botL         := (inferInstance : Bot (Fact locs))
    maxL         := _
    decEqL       := (inferInstance : DecidableEq (Fact locs))
    fhL          := (inferInstance : FiniteHeight (Fact locs))
    llL          := (inferInstance : SemiLattice (Fact locs))
    semantics    := semantics cfg hnd
    mono_absorb  := mono_absorb_coh
    edge_mono    := edgeTransfer_mono }

/-- Wrapper around `Chartreux.analyze`: run the bundled Nullability
    analysis directly on a `CFG`. -/
def analyzeCFG {locs : List Loc} (hnd : locs.Nodup)
    (cfg : WFCFG) :
    Chartreux.AnalysisResult (analysis hnd cfg) :=
  Chartreux.analyze (analysis hnd cfg)

/-- Turn-key correctness for the bundled nullability analysis: at every reachable
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
  exact Chartreux.Analysis.Generic.reachable_corr
    cfg.analysis
    A.semantics
    A.mono_absorb
    R.isPostFix
    R.inFacts_entry
    hreach

def checkExpr {locs : List Loc} (ℓ : Fact locs) : Expr -> Bool
  | .Null => true
  | .Int _ => true
  | .Var _ => true
  | .IsNull e => checkExpr ℓ e
  | .Not e =>
      checkExpr ℓ e && (evalExpr locs ℓ e == NVal.nonnull)
  | .BinOp _ e₁ e₂ =>
      checkExpr ℓ e₁ && checkExpr ℓ e₂ &&
      (evalExpr locs ℓ e₁ == NVal.nonnull) && (evalExpr locs ℓ e₂ == NVal.nonnull)

def checkNode {locs : List Loc} (ℓ : Fact locs) : NodeKind -> Bool
  | .Skip => true
  | .Assign _ e => checkExpr ℓ e
  | .Assume e => checkExpr ℓ e && (evalExpr locs ℓ e == NVal.nonnull)

def checkCFG (cfg : WFCFG) : Bool :=
  let locs := vars cfg
  let res := (analyzeCFG locs.prop cfg).inFacts
  (List.range cfg.val.nodes.length).all fun n =>
    match cfg.val.nodeKind n with
    | none => false
    | some kind => checkNode (res n) kind

end Duke.Analysis.Nullability

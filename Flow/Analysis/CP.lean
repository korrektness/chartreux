import Flow.Analysis.Generic
import Flow.Analysis.Worklist
import Flow.Lang.Eval
import Flow.Lang.CFG
import Mathlib.Data.List.Nodup

/-!
# Constant Propagation analysis instance

Instantiates the abstract worklist framework (`Flow.Analysis.Worklist`) for
the classical Constant-Propagation analysis over the small CFG defined in
`Flow.Lang.CFG`.

The per-variable abstract value `CPVal` is the standard three-point lattice

* `bot`     — "this variable is unreachable / not yet seen" (⊥);
* `const c` — "this variable definitely holds the integer constant `c`";
* `top`     — "this variable might hold any value" (⊤).

A whole-program *constant-propagation fact* `CPFact vars` is a function
`Fin vars.length → CPVal`, i.e.\ a `Domain vars.length CPVal`.  This re-uses
the generic `Domain` `FiniteHeight` instance from
`Flow.Analysis.Lattice`, giving a precise bound of `2 * vars.length`.
-/

namespace Flow.Analysis.CP

open Analysis
open Generic

/-! ## The per-variable lattice `CPVal` -/

/-- Abstract value tracked for a single variable. -/
inductive CPVal where
  | bot
  | const (n : Int)
  | top
  deriving DecidableEq, Repr

namespace CPVal

instance : Bot CPVal where
  bot := CPVal.bot

/-- Pointwise join on `CPVal`: `⊥` is the unit, `⊤` absorbs, two equal
    constants join to themselves, two distinct constants jump to `⊤`. -/
def join : CPVal → CPVal → CPVal
  | .bot,        v        => v
  | v,           .bot     => v
  | .top,        _        => .top
  | _,           .top     => .top
  | .const a,    .const b => if a = b then .const a else .top

instance : Max CPVal where
  max := join

/-- Height of `CPVal`: `bot ↦ 0`, `const _ ↦ 1`, `top ↦ 2`. -/
def height : CPVal → Nat
  | .bot     => 0
  | .const _ => 1
  | .top     => 2

@[simp] lemma join_bot_left (v : CPVal) : CPVal.bot ⊔ v = v := rfl
@[simp] lemma join_bot_right (v : CPVal) : v ⊔ CPVal.bot = v := by
  cases v <;> rfl
@[simp] lemma join_top_left (v : CPVal) : CPVal.top ⊔ v = CPVal.top := by
  cases v <;> rfl
@[simp] lemma join_top_right (v : CPVal) : v ⊔ CPVal.top = CPVal.top := by
  cases v <;> rfl

lemma join_comm (a b : CPVal) : a ⊔ b = b ⊔ a := by
  match a, b with
  | .bot,     v       => simp
  | v,        .bot    => simp
  | .top,     v       => simp
  | v,        .top    => simp
  | .const a, .const b =>
      by_cases hab : a = b
      · simp [hab]
      · simp [max, join, hab, Ne.symm hab]

lemma join_assoc (a b c : CPVal) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) := by
  -- `bot` is unit; `top` is absorbing; otherwise both sides reduce to a
  -- comparison of constants which is settled by `decide`/case-bash.
  match a, b, c with
  | .bot,     b,         c         => simp
  | a,        .bot,      c         => simp
  | a,        b,         .bot      => simp
  | .top,     b,         c         => simp
  | a,        .top,      c         => simp
  | a,        b,         .top      => simp
  | .const x, .const y,  .const z  => simp [max, join]; grind

lemma join_idem (a : CPVal) : a ⊔ a = a := by
  cases a with
  | bot     => rfl
  | const n => simp [max, join]
  | top     => rfl

lemma bot_le (a : CPVal) : a ⊔ CPVal.bot = a := join_bot_right a

/-- The `FiniteHeight` instance for `CPVal`.  Height is bounded by `2` and
    the join strictly increases the height whenever it changes the value. -/
instance : FiniteHeight CPVal where
  height := height
  maxHeight := 2
  maxHeight_ub
    | .bot     => by simp [height]
    | .const _ => by simp [height]
    | .top     => by simp [height]
  height_join a b h := by
    -- `h : ¬ (a ⊔ b = a)`.  We must show `height a < height (a ⊔ b)`.
    match a, b with
    | .bot, .bot         => exact absurd rfl h
    | .bot, .const _     => simp [height, Max.max, join]
    | .bot, .top         => simp [height, Max.max, join]
    | .const _, .bot     => exact absurd rfl h
    | .const _, .top     => simp [height, Max.max, join]
    | .top, .bot         => exact absurd rfl h
    | .top, .const _     => exact absurd rfl h
    | .top, .top         => exact absurd rfl h
    | .const a', .const b' =>
        by_cases hab : a' = b'
        · subst hab
          -- `h : ¬ (const a' ⊔ const a' = const a')` — but joins of equal
          -- constants reduce to `const a'`, so `h` is contradictory.
          exfalso; apply h
          show CPVal.const a' ⊔ CPVal.const a' = CPVal.const a'
          exact CPVal.join_idem _
        · simp [height, Max.max, join, hab]

instance : LatticeLike CPVal where
  join_comm  := join_comm
  join_assoc := join_assoc
  join_idem  := join_idem
  bot_le     := bot_le

end CPVal

/-! ## Whole-program facts: `CPFact vars` -/

/-- The list of variables ever assigned to or declared in `g`, in source
    order.  Duplicates are removed by `List.eraseDups`. -/
def varsInProgram (g : CFG) : List String :=
  (g.nodes.filterMap (fun k =>
    match k with
    | .Assign x _ => some x
    | .Decl x _   => some x
    | _           => none)).eraseDups

theorem List.mem_eraseDups {α} [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (a : α), a ∈ l.eraseDups ↔ a ∈ l
  | [], _ => by simp [List.eraseDups]
  | h :: t, a => by
    rw [List.eraseDups_cons]
    simp only [List.mem_cons]
    rw [mem_eraseDups (t.filter _) a, List.mem_filter]
    constructor
    · rintro (rfl | ⟨ha, _⟩)
      · exact Or.inl rfl
      · exact Or.inr ha
    · rintro (rfl | ha)
      · exact Or.inl rfl
      · by_cases heq : a = h
        · exact Or.inl heq
        · refine Or.inr ⟨ha, ?_⟩
          simp [heq]
termination_by l _ => l.length
decreasing_by grind [List.length_filter_le]

theorem eraseDups_nodup {α} [BEq α] [LawfulBEq α] : ∀ l : List α, l.eraseDups.Nodup
  | [] => by exact List.nodup_nil
  | h :: t => by
    rw [List.eraseDups_cons]
    refine List.Nodup.cons ?_ (eraseDups_nodup _)
    intro hmem
    rw [List.mem_eraseDups, List.mem_filter] at hmem
    grind
termination_by l => l.length
decreasing_by grind [List.length_filter_le]

/-- Index of variable `x` in the variable list `vars`, or `none` if `x`
    is not tracked. -/
def varIdx (vars : List String) (x : String) : Option (Fin vars.length) :=
  match vars.idxOf? x with
  | none   => none
  | some i =>
      if hi : i < vars.length then some ⟨i, hi⟩ else none

/-- A constant-propagation fact for a program with variable list `vars`
    is a `Domain` over `CPVal`. -/
abbrev CPFact (vars : List String) : Type := Domain vars.length CPVal

/-! ## Transfer functions -/

/-- Abstract evaluator for expressions under a CP fact.  This is a deliberately
    simple version that only propagates information through integer literals
    and variable lookups; arithmetic/relational expressions are conservatively
    sent to `⊤`.  The simplification keeps the monotonicity proof short while
    still exhibiting non-trivial constant-propagation behaviour at literal
    assignments such as `x := 1`. -/
def evalExpr (vars : List String) (ρ : CPFact vars) : Expr → CPVal
  | .Int n     => .const n
  | .Var x     =>
      match varIdx vars x with
      | none   => .top
      | some i => ρ i
  | .BinOp _ _ _ => .top

/-- Node transfer for Constant Propagation: on `Assign x e` / `Decl x e`,
    update the abstract value of `x` (joined with the existing one to keep
    the function monotone).  All other node kinds act as the identity. -/
def cpTransfer (vars : List String) (g : CFG) (n : NodeID) :
    CPFact vars → CPFact vars := fun ρ =>
  match g.nodeKind n with
  | some (.Assign x e) | some (.Decl x e) =>
      match varIdx vars x with
      | none   => ρ
      | some i =>
          let v := evalExpr vars ρ e
          fun j => if j = i then v else ρ j
  | _ => ρ

/-- Edge transfer for forward CP is the identity. -/
def cpEdgeTransfer (vars : List String) : Edge → CPFact vars → CPFact vars :=
  fun _ a => a

/-- The default initial fact: every tracked variable is `⊥`. -/
def cpEntryInit (vars : List String) : CPFact vars := fun _ => CPVal.bot

private lemma evalExpr_mono (vars : List String) (ρ₁ ρ₂ : CPFact vars)
    (hρ : ρ₁ ⊔ ρ₂ = ρ₁) (e : Expr) :
    evalExpr vars ρ₁ e ⊔ evalExpr vars ρ₂ e = evalExpr vars ρ₁ e := by
  have hpt : ∀ i, ρ₁ i ⊔ ρ₂ i = ρ₁ i := by
    intro i; have := congrFun hρ i; simpa [Domain.max_app] using this
  induction e with
  | Int n =>
    grind [evalExpr, CPVal.join_idem]
  | Var x =>
    simp only [evalExpr]
    split
    · exact CPVal.join_idem _
    · exact hpt _
  | BinOp op e₁ e₂ _ _ =>
    simp [evalExpr]

/-- Helper: combine four points by interleaved join. -/
private lemma four_join_eq (a b c d : CPVal)
    (hac : a ⊔ c = a) (hbd : b ⊔ d = b) :
    (a ⊔ b) ⊔ (c ⊔ d) = a ⊔ b := by
  have lc := CPVal.join_comm
  have la := CPVal.join_assoc
  calc
    (a ⊔ b) ⊔ (c ⊔ d)
        = ((a ⊔ c) ⊔ (b ⊔ d)) := by
          rw [la, ← la b, lc b c, la, ← la]
    _   = a ⊔ b := by rw [hac, hbd]

private lemma cpTransfer_mono (vars : List String) (g : CFG) (n : NodeID) :
    mono_f (cpTransfer vars g n) := by
  intro ρ₁ ρ₂ hxy
  have hpt : ∀ i, ρ₁ i ⊔ ρ₂ i = ρ₁ i := by
    intro i; have := congrFun hxy i; simpa [Domain.max_app] using this
  have hev : ∀ e, evalExpr vars ρ₁ e ⊔ evalExpr vars ρ₂ e = evalExpr vars ρ₁ e :=
    fun e => evalExpr_mono vars ρ₁ ρ₂ hxy e
  funext j
  change (cpTransfer vars g n ρ₁) j ⊔ (cpTransfer vars g n ρ₂) j
       = (cpTransfer vars g n ρ₁) j
  unfold cpTransfer
  generalize hk : g.nodeKind n = nk
  cases nk with
  | none => exact hpt j
  | some k =>
    cases k with
    | Cond _ | Skip => exact hpt j
    | Assign x e | Decl x e =>
      simp only
      generalize hx : varIdx vars x = a
      split <;> try split
      all_goals first | exact hpt j | exact hev e

private lemma cpEdgeTransfer_mono (vars : List String) :
    ∀ e, mono_f (cpEdgeTransfer vars e) := by
  intro _ x _ hxy; exact hxy

instance instTransferMonoCP (vars : List String) (g : CFG) :
    TransferMono (cpTransfer vars g) (cpEdgeTransfer vars) where
  node_mono := cpTransfer_mono vars g
  edge_mono := cpEdgeTransfer_mono vars

/-- Edges entering a node, computed by filtering `g.edges`. -/
def inEdges (g : CFG) (n : NodeID) : List Edge :=
  g.edges.filter (fun e => e.dst = n)

/-- Build a `Flow.Analysis.AnalysisCFG NodeID Edge` from a concrete `CFG`. -/
def forCFG (g : CFG)
    (hwf : ∀ n e, e ∈ inEdges g n → e.src < g.nodes.length) :
    AnalysisCFG NodeID Edge where
  nodes := List.range g.nodes.length
  edges := g.edges
  entry := g.entry
  exit  := g.exit
  srcOf e := e.src
  dstOf e := e.dst
  succ := g.succ
  pred := g.pred
  inEdges n := inEdges g n
  inEdges_src_mem := by
    intro n e he
    exact List.mem_range.mpr (hwf n e he)

section Corr
variable {vars : List String}

lemma vars_get_of_varIdx {x : String} {i : Fin vars.length}
    (h : varIdx vars x = some i) : vars.get i = x := by
  induction vars with
  | nil => simp [varIdx, List.idxOf?] at h
  | cons a t ih =>
    by_cases hax : a = x
    · subst hax
      simp only [List.length_cons, varIdx, List.idxOf?_cons, BEq.rfl, ↓reduceIte,
        Nat.zero_lt_succ, ↓reduceDIte, Fin.zero_eta, Option.some.injEq] at h
      simp [<- h]
    · obtain ⟨k, hk⟩ := i
      have hax' : (a == x) = false := by simp [hax]
      have hcons : (a :: t).idxOf? x = (t.idxOf? x).map (· + 1) := by
        simp [List.idxOf?_cons, hax']
      unfold varIdx at h
      rw [hcons] at h
      cases hkk : t.idxOf? x with
      | none => rw [hkk] at h; simp at h
      | some k' =>
        rw [hkk] at h
        simp only [Option.map_some] at h
        by_cases hk'lt : k' + 1 < (a :: t).length
        · rw [dif_pos hk'lt] at h
          have heq : k' + 1 = k := by
            injection h with h1
            exact (Fin.mk.inj_iff.mp h1).symm ▸ rfl
          have hk'lt' : k' < t.length := by
            simp [List.length_cons] at hk'lt; omega
          have ht : varIdx t x = some ⟨k', hk'lt'⟩ := by
            unfold varIdx; rw [hkk]; simp [hk'lt']
          have ihres := ih ht
          subst heq
          change (a :: t).get ⟨k' + 1, hk⟩ = x
          simpa using ihres
        · rw [dif_neg hk'lt] at h; simp at h
lemma not_mem_of_varIdx_none {x : String}
    (h : varIdx vars x = none) : x ∉ vars := by
  intro hx
  have : (vars.idxOf? x).isSome := List.isSome_idxOf?.mpr hx
  unfold varIdx at h
  cases h' : vars.idxOf? x with
  | none   => simp [h'] at this
  | some k =>
    rw [h'] at h
    by_cases hk : k < vars.length
    · simp [hk] at h
    · -- `idxOf? x = some k` always has `k < length`; eliminate the `else` branch.
      have : k < vars.length := by
        have := List.idxOf?_eq_map_finIdxOf?_val (xs := vars) (a := x)
        rw [h'] at this
        rcases hfi : vars.finIdxOf? x with _ | ⟨j, hj⟩ <;> grind
      exact absurd this hk

def cpβ (σ : CEK) : CPFact vars := fun i =>
  match σ.E (vars.get i) with
  | some (.Int v) => .const v
  | none          => .bot

def cpβVal : Val → CPVal
  | .Int n => .const n

def cpβ_corr (_ : CFG) (ℓ : CPFact vars) (σ : CEK) : Prop :=
  ℓ ⊑ (cpβ σ : CPFact vars)

lemma cpβ_corr_pw {ℓ : CPFact vars} {σ : CEK}
  (h : ℓ⊑(cpβ σ : CPFact vars)) (i : Fin vars.length) :
    ℓ i ⊔ cpβ σ i = ℓ i := by
  have := congrFun h i; simpa [Domain.max_app] using this

lemma evalExpr_sound {ρ : CPFact vars} {σ : CEK} {e : Expr} {v : Val}
    (hcorr : ρ⊑(cpβ σ : CPFact vars))
    (heval : EvalExpr σ.E e v) :
    evalExpr vars ρ e ⊔ cpβVal v = evalExpr vars ρ e := by
  -- "abstract over-approximates concrete", in `⊑`-form.
  induction heval with
  | int =>
    simp [evalExpr, cpβVal, CPVal.join_idem]
  | @var v x h =>
    cases v with
    | Int n =>
      simp only [evalExpr, cpβVal]
      cases hxi : varIdx vars x with
      | none =>
        simp
      | some i =>
        have hi : ρ i ⊔ cpβ σ i = ρ i := cpβ_corr_pw hcorr i
        have hget : vars.get i = x := vars_get_of_varIdx hxi
        have : cpβ σ i = .const n := by
          unfold cpβ
          rw [hget, h]
        rw [this] at hi; exact hi
  | binop _ _ _ _ =>
    simp [evalExpr]

def cpDFA (vars : List String) : DFA where
  L        := CPFact vars
  transfer := cpTransfer vars
  entry    := fun _ => cpEntryInit vars

def cpSemantics (vars : List String) (hnd : vars.Nodup) :
    DFASemantics (cpDFA vars) where
  Corr := cpβ_corr
  preserve_id := by
    intros _g _n ℓ σ σ' _hnm heq hcorr
    simp [cpβ_corr]
    have : (cpβ σ' : CPFact vars) = cpβ σ := by
      funext i; unfold cpβ; rw [heq]
    simpa [this] using hcorr
  preserve_assign := by
    intros g' n ℓ σ σ' x e v hmut heval heq hcorr
    simp only [cpβ_corr]
    generalize h : ((cpDFA vars).transfer g' n ℓ) = ℓ'
    have hkind :
        g'.nodeKind n = some (.Assign x e) ∨ g'.nodeKind n = some (.Decl x e) := hmut
    funext j
    simp only [Domain.max_app]
    cases hxi : varIdx vars x with
    | none =>
      have hx_notin : x ∉ vars := not_mem_of_varIdx_none hxi
      have hne : vars.get j ≠ x := fun h => hx_notin (h ▸ List.get_mem ..)
      have hβ : cpβ σ' j = cpβ σ j := by
        unfold cpβ
        have : σ'.E (vars.get j) = σ.E (vars.get j) := by
          simp [heq, State.updated]
          grind
        rw [this]
      have htr : (cpDFA vars).transfer g' n ℓ j = ℓ j := by
        change cpTransfer vars g' n ℓ j = ℓ j
        unfold cpTransfer
        rcases hkind with h | h <;> rw [h] <;> simp [hxi]
      rw [<- h, htr, hβ]; exact cpβ_corr_pw hcorr j
    | some i =>
      have hgetx : vars.get i = x := vars_get_of_varIdx hxi
      have htr_i : (cpDFA vars).transfer g' n ℓ i = evalExpr vars ℓ e := by
        change cpTransfer vars g' n ℓ i = _
        unfold cpTransfer
        rcases hkind with h | h <;> rw [h] <;> simp [hxi]
      have htr_off : ∀ j, j ≠ i →
          (cpDFA vars).transfer g' n ℓ j = ℓ j := by
        intro j hji
        change cpTransfer vars g' n ℓ j = ℓ j
        unfold cpTransfer
        rcases hkind with h | h <;> rw [h] <;> simp [hxi, hji]
      by_cases hji : j = i
      · subst hji
        cases v with
        | Int n =>
          have hβ : cpβ σ' j = .const n := by
            unfold cpβ
            have : σ'.E (vars.get j) = some (.Int n) := by
              rw [heq, hgetx]; unfold State.updated; simp
            rw [this]
          rw [hβ]
          grind [cpβVal, evalExpr_sound hcorr heval]
      · have htr_j : ℓ' j = ℓ j := by rw [← h]; exact htr_off j hji
        have hgetj_ne : vars.get j ≠ x := by
          intro hgj
          have : vars.get j = vars.get i := by rw [hgj, hgetx]
          have hji_eq : j = i := by
            apply Fin.eq_of_val_eq
            exact (List.Nodup.getElem_inj_iff hnd).mp this
          exact hji hji_eq
        have hβ : cpβ σ' j = cpβ σ j := by
          unfold cpβ
          have : σ'.E (vars.get j) = σ.E (vars.get j) := by
            rw [heq]; unfold State.updated
            exact if_neg (fun hxj => hgetj_ne hxj.symm)
          rw [this]
        rw [htr_j, hβ]; exact cpβ_corr_pw hcorr j
end Corr
end Flow.Analysis.CP

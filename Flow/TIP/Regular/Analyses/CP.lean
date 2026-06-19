import Flow.Analysis.Generic
import Flow.Analysis.Worklist
import Flow.Analysis.WorklistProofs
import Flow.TIP.Eval
import Flow.TIP.Regular.CFG
import Flow.TIP.Regular.LangSem
import Mathlib.Data.List.Nodup

namespace Flow.Analysis.CP

open Analysis
open Generic
open Flow.TIP (tipLStep tipLStutter tipLangSem forCFG WFCFG)

/-- Abstract value for a single variable -/
inductive CPVal where
  | bot
  | const (n : Int)
  | top
  deriving DecidableEq, Repr

instance : ToString CPVal where
  toString
    | .bot     => "⊥"
    | .top     => "⊤"
    | .const n => toString n

instance {v : List String} : ToString (Domain v.length CPVal) where
  toString ρ :=
    let parts : List String :=
      (List.finRange v.length).map fun i =>
        v.get i ++ "=" ++ toString (ρ i)
    "[" ++ String.intercalate ", " parts ++ "]"

namespace CPVal

instance : Bot CPVal where
  bot := CPVal.bot

def join : CPVal -> CPVal -> CPVal
  | .bot,        v        => v
  | v,           .bot     => v
  | .top,        _        => .top
  | _,           .top     => .top
  | .const a,    .const b => if a = b then .const a else .top

instance : Max CPVal where
  max := join

def remainingHeight : CPVal -> Nat
  | .bot     => 2
  | .const _ => 1
  | .top     => 0

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

lemma bot_le (a : CPVal) : CPVal.bot ⊑ a := join_bot_left a

/-- `FiniteHeight` for CPVal : bounded by 2. -/
instance : FiniteHeight CPVal where
  remainingHeight := remainingHeight
  height_join a b h := by
    -- `h : ¬ (a ⊔ b = a)`.  We must show `height a < height (a ⊔ b)`.
    match a, b with
    | .bot, .bot         => exact absurd rfl h
    | .bot, .const _     => simp [remainingHeight, Max.max, join]
    | .bot, .top         => simp [remainingHeight, Max.max, join]
    | .const _, .bot     => exact absurd rfl h
    | .const _, .top     => simp [remainingHeight, Max.max, join]
    | .top, .bot         => exact absurd rfl h
    | .top, .const _     => exact absurd rfl h
    | .top, .top         => exact absurd rfl h
    | .const a', .const b' =>
        by_cases hab : a' = b'
        · subst hab
          exfalso; apply h
          show CPVal.const a' ⊔ CPVal.const a' = CPVal.const a'
          exact CPVal.join_idem _
        · simp [remainingHeight, Max.max, join, hab]

instance : LatticeLike CPVal where
  join_comm  := join_comm
  join_assoc := join_assoc
  join_idem  := join_idem
  bot_le     := bot_le

end CPVal


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

def evalExpr (vars : List String) (ρ : CPFact vars) : Expr -> CPVal
  | .Int n     => .const n
  | .Var x     =>
      match varIdx vars x with
      | none   => .top
      | some i => ρ i
  | .BinOp op e₁ e₂ =>
      match evalExpr vars ρ e₁, evalExpr vars ρ e₂ with
      | .const n₁, .const n₂ => .const (applyOp op n₁ n₂)
      | .bot,      _         => .bot
      | _,         .bot      => .bot
      | _,         _         => .top

def cpTransfer (vars : List String) (g : CFG) (n : NodeID) :
    CPFact vars -> CPFact vars := fun ρ =>
  match g.nodeKind n with
  | some (.Assign x e) | some (.Decl x e) =>
      match varIdx vars x with
      | none   => ρ
      | some i =>
          let v := evalExpr vars ρ e
          fun j => if j = i then v else ρ j
  | _ => ρ

/-- Edge transfer for forward CP is the identity. -/
def cpEdgeTransfer (vars : List String) : Edge -> CPFact vars -> CPFact vars :=
  fun _ a => a

/-- The default initial fact: every tracked variable is `⊥`. -/
def cpEntryInit (vars : List String) : CPFact vars := fun _ => CPVal.bot

private lemma const_absorbs_inv {n : Int} {a : CPVal}
    (h : a ⊑ CPVal.const n) : a = .bot ∨ a = .const n := by
  cases a with
  | bot => exact Or.inl rfl
  | const m => simp [Max.max, CPVal.join] at h; grind
  | top => simp at h

private lemma evalExpr_mono (vars : List String) (ρ₁ ρ₂ : CPFact vars)
    (hρ : ρ₁ ⊑ ρ₂) (e : Expr) :
    evalExpr vars ρ₁ e ⊑ evalExpr vars ρ₂ e := by
  have hpt : ∀ i, ρ₁ i ⊑ ρ₂ i := by
    intro i; have := congrFun hρ i; simpa [Domain.max_app] using this
  induction e with
  | Int n =>
    grind [evalExpr, CPVal.join_idem]
  | Var x =>
    simp only [evalExpr]
    split
    · exact CPVal.join_idem _
    · exact hpt _
  | BinOp op e₁ e₂ ih₁ ih₂ =>
    simp only [evalExpr]
    cases ha₁ : evalExpr vars ρ₁ e₁ <;>
      cases hb₁ : evalExpr vars ρ₁ e₂ <;>
      cases ha₂ : evalExpr vars ρ₂ e₁ <;>
      cases hb₂ : evalExpr vars ρ₂ e₂ <;>
      rw [ha₁, ha₂] at ih₁ <;>
      rw [hb₁, hb₂] at ih₂ <;>
      simp_all [Max.max, CPVal.join]


private lemma cpTransfer_mono (vars : List String) (g : CFG) (n : NodeID) :
    mono_f (cpTransfer vars g n) := by
  intro ρ₁ ρ₂ hxy
  have hpt : ∀ i, ρ₁ i ⊑ ρ₂ i := by
    intro i; have := congrFun hxy i; simpa [Domain.max_app] using this
  have hev : ∀ e, evalExpr vars ρ₁ e ⊑ evalExpr vars ρ₂ e :=
    fun e => evalExpr_mono vars ρ₁ ρ₂ hxy e
  funext j
  change (cpTransfer vars g n ρ₁) j ⊑ (cpTransfer vars g n ρ₂) j
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
    ∀ e, mono_f (cpEdgeTransfer vars e) := fun _ _ _ h => h

instance instTransferMonoCP (vars : List String) (cfg : WFCFG) :
  TransferMono (cpTransfer vars cfg) (cpEdgeTransfer vars) where
    node_mono := cpTransfer_mono vars cfg
    edge_mono := cpEdgeTransfer_mono vars

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

def cpβ (σ : State) : CPFact vars := fun i =>
  match σ (vars.get i) with
  | some (.Int v) => .const v
  | none          => .bot

def cpβVal : Val -> CPVal
  | .Int n => .const n

def cpβ_corr (ℓ : CPFact vars) (σ : State) : Prop :=
  cpβ σ ⊑ ℓ

lemma cpβ_corr_pw {ℓ : CPFact vars} {σ : State}
  (h : cpβ σ ⊑ ℓ) (i : Fin vars.length) :
    cpβ σ i ⊑ ℓ i := by
  have := congrFun h i; simpa [Domain.max_app] using this

lemma evalExpr_sound {ρ : CPFact vars} {σ : State} {e : Expr} {v : Val}
    (hcorr : cpβ σ ⊑ ρ)
    (heval : EvalExpr σ e v) :
    cpβVal v ⊑ evalExpr vars ρ e := by
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
        have hi : cpβ σ i ⊑ ρ i := cpβ_corr_pw hcorr i
        have hget : vars.get i = x := vars_get_of_varIdx hxi
        have : cpβ σ i = .const n := by
          unfold cpβ
          rw [hget, h]
        rw [this] at hi; exact hi
  | @binop e₁ n₁ e₂ n₂ o _ _ ih₁ ih₂ =>
    simp only [evalExpr, cpβVal] at *
    cases ha : evalExpr vars ρ e₁ <;>
      cases hb : evalExpr vars ρ e₂ <;>
      rw [ha] at ih₁ <;>
      rw [hb] at ih₂ <;>
      simp_all [Max.max, CPVal.join]

/-- The DFA closure for CP, parameterised by the underlying TIP CFG. -/
def cpDFA (vars : List String) (cfg : WFCFG) : DFA NodeID Edge where
  L            := CPFact vars
  nodeTransfer := cpTransfer vars cfg
  edgeTransfer := cpEdgeTransfer vars
  entry        := cpEntryInit vars

@[simp] private lemma cpDFA_transferAlong (vars : List String) (cfg : WFCFG)
    (e : EdgeOf cfg.analysis) (ℓ : CPFact vars) :
    (cpDFA vars cfg).transferAlong cfg.analysis e ℓ =
    cpTransfer vars cfg e.val.src ℓ := rfl

/-- Internal lemma: the env-update + Assign/Decl case of `preserve_step`.
    Shared between Assign and Decl since they have the same shape. -/
private lemma cp_preserve_assign_case (vars : List String) (hnd : vars.Nodup)
    (cfg : CFG) (n : NodeID) (ℓ : CPFact vars) (σ σ' : State)
    (x : String) (e : Expr) (v : Val)
    (hkind : cfg.nodeKind n = some (.Assign x e) ∨ cfg.nodeKind n = some (.Decl x e))
    (heval : EvalExpr σ e v)
    (heq : σ' = σ.updated x v)
    (hcorr : cpβ_corr ℓ σ) :
    cpβ_corr (cpTransfer vars cfg n ℓ) σ' := by
  simp only [cpβ_corr]
  generalize h : (cpTransfer vars cfg n ℓ) = ℓ'
  funext j
  simp only [Domain.max_app]
  cases hxi : varIdx vars x with
  | none =>
    have hx_notin : x ∉ vars := not_mem_of_varIdx_none hxi
    have hne : vars.get j ≠ x := fun h => hx_notin (h ▸ List.get_mem ..)
    have hβ : cpβ σ' j = cpβ σ j := by
      unfold cpβ
      have : σ' (vars.get j) = σ (vars.get j) := by
        simp [heq, State.updated]; grind
      rw [this]
    have htr : cpTransfer vars cfg n ℓ j = ℓ j := by
      unfold cpTransfer
      rcases hkind with hh | hh <;> rw [hh] <;> simp [hxi]
    rw [<- h, htr, hβ]; exact cpβ_corr_pw hcorr j
  | some i =>
    have hgetx : vars.get i = x := vars_get_of_varIdx hxi
    have htr_i : cpTransfer vars cfg n ℓ i = evalExpr vars ℓ e := by
      unfold cpTransfer
      rcases hkind with hh | hh <;> rw [hh] <;> simp [hxi]
    have htr_off : ∀ j, j ≠ i -> cpTransfer vars cfg n ℓ j = ℓ j := by
      intro j hji
      unfold cpTransfer
      rcases hkind with hh | hh <;> rw [hh] <;> simp [hxi, hji]
    by_cases hji : j = i
    · subst hji
      cases v with
      | Int m =>
        have hβ : cpβ σ' j = .const m := by
          unfold cpβ
          have : σ' (vars.get j) = some (.Int m) := by
            rw [heq, hgetx]; unfold State.updated; simp
          rw [this]
        rw [hβ, <- h, htr_i]
        have hev := evalExpr_sound hcorr heval
        simpa [cpβVal] using hev
    · have htr_j : ℓ' j = ℓ j := by rw [<- h]; exact htr_off j hji
      have hgetj_ne : vars.get j ≠ x := by
        intro hgj
        have : vars.get j = vars.get i := by rw [hgj, hgetx]
        have hji_eq : j = i := by
          apply Fin.eq_of_val_eq
          exact (List.Nodup.getElem_inj_iff hnd).mp this
        exact hji hji_eq
      have hβ : cpβ σ' j = cpβ σ j := by
        unfold cpβ
        have : σ' (vars.get j) = σ (vars.get j) := by
          rw [heq]; unfold State.updated
          exact if_neg (fun hxj => hgetj_ne hxj.symm)
        rw [this]
      rw [htr_j, hβ]; exact cpβ_corr_pw hcorr j

/-- Internal lemma: the branch / advance (skip) case of `preserve_step`.
    Whenever the source node's `cpTransfer` is the identity (Cond,
    Skip, etc.) and the env doesn't change, correctness is preserved. -/
private lemma cp_preserve_branch_case (vars : List String) (cfg : CFG)
    (n : NodeID) (ℓ : CPFact vars) (σ : State)
    (htr_id : cpTransfer vars cfg n ℓ = ℓ)
    (hcorr : cpβ_corr ℓ σ) :
    cpβ_corr (cpTransfer vars cfg n ℓ) σ := by grind [cpβ_corr]

/-- The CP `DFASemantics` for a fixed TIP CFG. The three preservation
    fields directly consume the abstract `LangSem` transitions. -/
def cpSemantics (vars : List String) (hnd : vars.Nodup) (cfg : WFCFG) :
    DFASemantics (ls := tipLangSem cfg) cfg.analysis (cpDFA vars cfg) :=
  { Corr := cpβ_corr
    isInit := State.isInit
    preserve_entry := by
      intro σ hinit
      cases hinit
      change cpEntryInit vars ⊑ cpβ State.empty
      funext i
      simp [Domain.max_app, cpEntryInit, cpβ, State.empty]

    preserve_step := by
      intro e σ σ' ℓ hstep hcorr
      simp only [cpDFA_transferAlong, cpTransfer]
      rcases hstep with ⟨x, e', v, hassign, heval, hEupd⟩
                      | ⟨c, v, hbr, _heval, _hbt, hE⟩
                      | ⟨hskip, _hkind, hE⟩
      · exact cp_preserve_assign_case vars hnd cfg e.val.src ℓ σ σ' x e' v
          hassign heval hEupd hcorr
      · -- Cond is identity for `cpTransfer`.
        have htr_id : cpTransfer vars cfg e.val.src ℓ = ℓ := by
          funext j; unfold cpTransfer; rw [hbr]
        simpa [hE] using cp_preserve_branch_case vars cfg e.val.src ℓ σ htr_id hcorr
      · -- Skip is identity for `cpTransfer`.
        have htr_id : cpTransfer vars cfg e.val.src ℓ = ℓ := by
          funext j; unfold cpTransfer; rw [hskip]
        simpa [hE] using cp_preserve_branch_case vars cfg e.val.src ℓ σ htr_id hcorr
    preserve_stutter := by
      intro _n σ σ' ℓ hstut hcorr
      -- `LStutter` boils down to `σ'.E = σ.E`.
      change σ' = σ at hstut
      simp only [cpβ_corr] at *
      have hβ : (cpβ σ' : CPFact vars) = cpβ σ := by
        funext i; unfold cpβ; rw [hstut]
      simpa [hβ] using hcorr }

theorem mono_absorb_cp
    {ℓ ℓ' : CPFact vars} {σ : State} (h : ℓ ⊑ ℓ')
    (hcorr : cpβ_corr ℓ σ) : cpβ_corr ℓ' σ := by
  simp only [cpβ_corr] at *
  funext i
  simp only [Domain.max_app]
  have hi : ℓ i ⊑ ℓ' i := by
    have := congrFun h i; simpa [Domain.max_app] using this
  have hci : cpβ σ i ⊑ ℓ i := by
    have := congrFun hcorr i; simpa [Domain.max_app] using this
  calc cpβ σ i ⊔ ℓ' i
      = cpβ σ i ⊔ (ℓ i ⊔ ℓ' i) := by rw [hi]
    _ = (cpβ σ i ⊔ ℓ i) ⊔ ℓ' i := by rw [CPVal.join_assoc]
    _ = ℓ i ⊔ ℓ' i := by rw [hci]
    _ = ℓ' i := hi

end Corr

/-! ## Bundled CP analysis -/

/-- A bundled `Flow.Analysis` for constant propagation, parameterized by
    the variable list, a `Nodup` proof, and the underlying TIP CFG. -/
def cpAnalysis (vars : List String) (hnd : vars.Nodup) (cfg : WFCFG) :
    Flow.Analysis (g := cfg.analysis) NodeID Edge State :=
  { dfa          := cpDFA vars cfg
    botL         := (inferInstance : Bot (CPFact vars))
    maxL         := (inferInstance : Max (CPFact vars))
    decEqL       := (inferInstance : DecidableEq (CPFact vars))
    fhL          := (inferInstance : FiniteHeight (CPFact vars))
    llL          := (inferInstance : LatticeLike (CPFact vars))
    semantics    := cpSemantics vars hnd cfg
    mono_absorb  := mono_absorb_cp
    transferMono := instTransferMonoCP vars cfg}

/-- TIP-facing wrapper around `Flow.analyze`: run the bundled CP
    analysis directly on a TIP `CFG`. -/
def cpAnalyzeCFG (vars : List String) (hnd : vars.Nodup) (cfg : WFCFG) :=
  Flow.analyze (cpAnalysis vars hnd cfg)

/-- Turn-key correctness for the bundled CP analysis: at every reachable
    program point, the computed in-fact correctly approximates the
    concrete state. -/
theorem cp_reachable_correct
    {vars : List String} (hnd : vars.Nodup)
    (cfg : WFCFG) :
    ∀ {n : NodeID} {σ : State},
      Flow.Analysis.Generic.Reachable cfg.analysis n σ State.isInit ->
        cpβ_corr ((cpAnalyzeCFG vars hnd cfg).inFacts n) σ := by
  intro n σ hreach
  let A := cpAnalysis vars hnd cfg
  let R := cpAnalyzeCFG vars hnd cfg
  letI := A.maxL
  exact Flow.Analysis.Generic.reachable_corr
    cfg.analysis
    A.semantics
    A.mono_absorb
    R.isPostFix
    R.inFacts_entry
    hreach

end Flow.Analysis.CP

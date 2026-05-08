import Flow.Lang.CFG
import Flow.Lang.Eval

namespace Flow.Eval.Refinement

def NodeAssigns (g : CFG) (n : NodeID) (x : String) (e : Expr) : Prop :=
  g.nodeKind n = some (.Assign x e) ∨ g.nodeKind n = some (.Decl x e)

def NodeMutates (g : CFG) (n : NodeID) : Prop :=
  ∃ x e, NodeAssigns g n x e

def NodeNonMutating (g : CFG) (n : NodeID) : Prop :=
  (∀ x e, g.nodeKind n ≠ some (.Assign x e)) ∧
  (∀ x e, g.nodeKind n ≠ some (.Decl x e))

/-- A `Cond` node guarded by `c` whose guard evaluates to `v`. -/
def NodeBranches (g : CFG) (n : NodeID) (c : Expr) : Prop :=
  g.nodeKind n = some (.Cond c)

def BranchTaken : EdgeKind → Val → Prop
  | .TBranch, .Int n => n ≠ 0
  | .FBranch, .Int 0 => True
  | _,        _       => False

/-! ## `StepN` — the indexed companion of `Step`

`StepN` packages a CEK step with pointer to valid CFG nodes. -/
inductive StepN (g : CFG) :
    {n : Nat} → n < g.nodes.length → CEK →
    {n' : Nat} → n' < g.nodes.length → CEK → Prop where
-- no change
| stutter {n : Nat} (h : n < g.nodes.length) {σ σ' : CEK} :
    Step σ σ' →
    σ'.E = σ.E →
    StepN g h σ h σ'
-- change in environment
| mutate {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
    {σ σ' : CEK} (x : String) (e : Expr) (v : Val) :
    Step σ σ' →
    NodeAssigns g n x e →
    EvalExpr σ.E e v ->
    (∃ k, g.hasEdge n n' k) →
    σ'.E = σ.E.updated x v →
    StepN g h σ h' σ'
-- cond step
| branch {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
    {σ σ' : CEK} (c : Expr) (k : EdgeKind) (v : Val) :
    Step σ σ' →
    NodeBranches g n c →
    g.hasEdge n n' k →
    EvalExpr σ.E c v →
    BranchTaken k v →
    σ'.E = σ.E →
    StepN g h σ h' σ'
-- skip
| advance {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
    {σ σ' : CEK} :
    Step σ σ' →
    g.nodeKind n = some .Skip →
    g.hasEdge n n' .Normal →
    σ'.E = σ.E →
    StepN g h σ h' σ'

/-- projection: a decorated step is, in particular, a step. -/
theorem StepN.toStep {g : CFG}
    {n n' : Nat} {h : n < g.nodes.length} {h' : n' < g.nodes.length}
    {σ σ' : CEK} (hsim : StepN g h σ h' σ') : Step σ σ' := by
  cases hsim with
  | stutter _ hstep _ => exact hstep
  | mutate _ _ _ _ _ hstep _ _ _ => exact hstep
  | branch _ _ _ _ _ hstep _ _ _ _ _ => exact hstep
  | advance _ _ hstep _ _ _ => exact hstep

/-- Reflexive/transitive closure of Steps -/
inductive StepsN (g : CFG) :
    {n : Nat} → n < g.nodes.length → CEK →
    {n' : Nat} → n' < g.nodes.length → CEK → Prop where
  | refl {n : Nat} (h : n < g.nodes.length) (σ : CEK) :
      StepsN g h σ h σ
  | step {n n₁ n' : Nat}
      (h : n < g.nodes.length) (h₁ : n₁ < g.nodes.length)
      (h' : n' < g.nodes.length) {σ σ₁ σ' : CEK} :
      StepN g h σ h₁ σ₁ → StepsN g h₁ σ₁ h' σ' →
      StepsN g h σ h' σ'
  -- step-to-normal
  | skipBridge {n n₁ n' : Nat}
      (h : n < g.nodes.length) (h₁ : n₁ < g.nodes.length)
      (h' : n' < g.nodes.length) {σ σ' : CEK} :
      g.nodeKind n = some .Skip →
      g.hasEdge n n₁ .Normal →
      StepsN g h₁ σ h' σ' →
      StepsN g h σ h' σ'

/-- Lift a single `StepN` to a `StepsN`. -/
def StepsN.single {g : CFG} {n n' : Nat}
    (h : n < g.nodes.length) (h' : n' < g.nodes.length)
    {σ σ' : CEK} (hsn : StepN g h σ h' σ') : StepsN g h σ h' σ' :=
  .step h h' h' hsn (.refl h' σ')

/-- Transitivity of `StepsN`: append two derivations. -/
theorem StepsN.trans {g : CFG}
    {n n₁ n' : Nat}
    {h : n < g.nodes.length} {h₁ : n₁ < g.nodes.length}
    {h' : n' < g.nodes.length} {σ σ₁ σ' : CEK}
    (hl : StepsN g h σ h₁ σ₁) (hr : StepsN g h₁ σ₁ h' σ') :
    StepsN g h σ h' σ' := by
  induction hl with
  | refl _ _ => exact hr
  | step h h_mid h_end hsn _ ih =>
    exact .step h h_mid h' hsn (ih hr)
  | skipBridge h h_mid h_end hk hedge _ ih =>
    exact .skipBridge h h_mid h' hk hedge (ih hr)

/-! ## `step_decorate` — every `Step` lifts from a `LocatedAt` to a `StepN`

See `Flow/Eval/Located.lean` for `LocatedAt` / `KontMatches`. -/

/-- A CEK state that is structurally "initial": empty environment and
    empty continuation stack. The component `σ.C` is unconstrained so the
    predicate is independent of any source program. -/
def IsInitial (_ : CFG) (σ : CEK) : Prop :=
  σ.E = State.empty ∧ σ.K = []

end Flow.Eval.Refinement

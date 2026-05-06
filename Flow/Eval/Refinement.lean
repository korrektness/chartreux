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

/-- Predicate selecting which CFG edge kind is consistent with a guard
    value `v`. The T-edge is taken on any non-zero integer; the F-edge on
    `0`. Other edge kinds out of a `Cond` node are not taken (the CFG
    builder never generates them anyway). -/
def BranchTaken : EdgeKind → Val → Prop
  | .TBranch, .Int n => n ≠ 0
  | .FBranch, .Int 0 => True
  | _,        _       => False

/-! ## `StepN` — the indexed companion of `Step`

`StepN g n h σ n' h' σ'` packages a single CEK step `σ ⟶ σ'` together with
the CFG node `n` it originates from and the node `n'` it advances to. It is
*not* a redefinition of the operational semantics: every constructor has
the underlying `Step σ σ'` as a premise.

For pragmatic concision we expose only the two distinctions that the
generic simulation actually needs:

* `stutter`  — the step does not change the environment and stays at `n`;
* `mutate`   — the step writes back an `Assign`/`Decl` value, advances
               along a CFG edge, and corresponds to a `NodeMutates n` node.

These two shapes, together, are enough to discharge any §2.2-style
forward-analysis correctness argument: the analysis only needs to know
"node mutates → use `transfer_correct`" or "node does not mutate → use
`transfer_id_correct`". Branching/loop-edge information beyond that is
recovered from the CFG post-fixpoint hypothesis. -/
inductive StepN (g : CFG) :
    {n : Nat} → n < g.nodes.length → CEK →
    {n' : Nat} → n' < g.nodes.length → CEK → Prop where
  /-- Stutter: the underlying `Step` leaves the environment unchanged
      and we stay at `n`. The earlier `NodeNonMutating g n` premise was
      dropped because it is overly restrictive: many CEK steps that
      *originate at* a mutating node (e.g. `Step.Decl`/`Step.Assign`,
      which only enter rhs evaluation without writing back) are
      env-preserving and need to lift to `StepN`. The semantics
      framework's `preserve_id` obligation never used the
      non-mutating premise — see `Flow.Analysis.Generic.DFASemantics`. -/
  | stutter {n : Nat} (h : n < g.nodes.length) {σ σ' : CEK} :
      Step σ σ' →
      σ'.E = σ.E →
      StepN g h σ h σ'
  /-- Mutating writeback: the underlying `Step` performs the writeback for
      an `Assign x e`/`Decl x e` node. The step advances along a CFG edge
      to `n'` and produces an environment that differs at exactly `x`. -/
  | mutate {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
      {σ σ' : CEK} (x : String) (e : Expr) (v : Val) :
      Step σ σ' →
      NodeAssigns g n x e →
      EvalExpr σ.E e v ->
      (∃ k, g.hasEdge n n' k) →
      σ'.E = σ.E.updated x v →
      StepN g h σ h' σ'
  /-- Branching: the underlying `Step` originates from a `Cond` node whose
      guard evaluates to `v`, the CFG advances to `n'` along the
      `TBranch`/`FBranch` edge selected by `v`, and the environment is
      preserved. This decoration retains the guard / value / edge-kind
      witnesses so that flow-sensitive analyses (sign, interval, etc.) can
      refine their abstract state along each branch. -/
  | branch {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
      {σ σ' : CEK} (c : Expr) (k : EdgeKind) (v : Val) :
      Step σ σ' →
      NodeBranches g n c →
      g.hasEdge n n' k →
      EvalExpr σ.E c v →
      BranchTaken k v →
      σ'.E = σ.E →
      StepN g h σ h' σ'
  /-- Node-advancing without writeback: the underlying `Step` originates
      from a `.Skip` node, preserves the environment, and follows a
      `.Normal` CFG edge to `n'`. Used by `Step.SeqMid` and `Step.WhileD`,
      which neither mutate nor branch. -/
  | advance {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
      {σ σ' : CEK} :
      Step σ σ' →
      g.nodeKind n = some .Skip →
      g.hasEdge n n' .Normal →
      σ'.E = σ.E →
      StepN g h σ h' σ'

/-- Forgetful projection: a decorated step is, in particular, a step. -/
theorem StepN.toStep {g : CFG}
    {n n' : Nat} {h : n < g.nodes.length} {h' : n' < g.nodes.length}
    {σ σ' : CEK} (hsim : StepN g h σ h' σ') : Step σ σ' := by
  cases hsim with
  | stutter _ hstep _ => exact hstep
  | mutate _ _ _ _ _ hstep _ _ _ => exact hstep
  | branch _ _ _ _ _ hstep _ _ _ _ _ => exact hstep
  | advance _ _ hstep _ _ _ => exact hstep

/-! ## Reflexive-transitive closure of `StepN` -/

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
  /-- Skip-bridge: the CFG advances along a `.Normal` edge between two
      `.Skip` nodes without consuming a CEK step. Used when the kont
      structure (`KontMatches.skipBridge`) records bridging through the
      merge `Skip` inserted by `BuildSpec.if_`/`while_`. -/
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

end Flow.Eval.Refinement

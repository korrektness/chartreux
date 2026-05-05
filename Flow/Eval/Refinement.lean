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
  /-- Stutter: the underlying `Step` leaves the environment unchanged,
      the CFG node `n` is non-mutating, and we stay at `n`. -/
  | stutter {n : Nat} (h : n < g.nodes.length) {σ σ' : CEK} :
      Step σ σ' →
      NodeNonMutating g n →
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

/-- Forgetful projection: a decorated step is, in particular, a step. -/
theorem StepN.toStep {g : CFG}
    {n n' : Nat} {h : n < g.nodes.length} {h' : n' < g.nodes.length}
    {σ σ' : CEK} (hsim : StepN g h σ h' σ') : Step σ σ' := by
  cases hsim with
  | stutter _ hstep _ _ => exact hstep
  | mutate _ _ _ _ _ hstep _ _ _ => exact hstep

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

end Flow.Eval.Refinement

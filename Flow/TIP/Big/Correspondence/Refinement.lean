import Flow.TIP.Big.CFG
import Flow.TIP.Eval
import Flow.TIP.Regular.Correspondence.Refinement

/-!
# `BigStepN` / `BigStepsN` — env-aware companions of `Step` for `BigCFG`

Mirrors `Flow.Eval.Refinement` for the regular CFG, with the same five-way
split (`stutter` / `mutate` / `branch` / `advance` + structural
`skipBridge`). The difference is in how the CFG-level move maps to CEK
work:

* **Regular CFG.** Each non-`Skip` node *is* the statement (`Assign x e`,
  `Cond c`, etc.). A `mutate` step packages the writeback `Step.AssignD`;
  the surrounding expression-evaluation and frame-push CEK steps are
  absorbed by `stutter` *at the same node*.
* **Big CFG.** Each statement is unfolded into four nodes
  `SEntry s → EEntry e → EExit → SExit`, with the source/exit edges being
  `Normal` and condition-driven branches leaving the `EExit` of the guard
  expression. Same step shape — `stutter` covers the in-node CEK work,
  the four edge-consuming constructors mirror the regular ones.

Stuttering carries more weight here than in the regular case:
* expression-evaluation Steps stutter at `EEntry`;
* `.SeqEnter` stutters at the (shared) `SEntry s₁` of `Seq s₁ s₂`;
* `.WhileD; .WhileC; eval c` stutter at `SExit body` before the
  `SExit body → EExit c` back-edge fires as a `skipBridge`.

Symmetric to the regular `skipBridge`, the bridge here is a zero-CEK-step
move along a `Normal` edge that advances the program counter when source
and destination are CEK-shape-compatible. The legitimate uses are
`EEntry → EExit`, `SExit body → EExit c` (while back), and
`SExit → SExit` (if-merges).
-/

namespace Flow.Eval.Big.Refinement

open Flow.Eval.Refinement (BranchTaken)

/-! ## Static predicates over `BigCFG`

Static replacements for `NodeAssigns` / `NodeBranches`: in the regular
CFG a single node carries the statement info; in the big CFG it is split
across a `SEntry` → `EEntry` → `EExit` chain, so we recover the same
information by walking that chain. -/

/-- `BigNodeWritesback g n x e`: `n` is an `EExit` whose enclosing
    statement writes back `e` into `x` — either `Assign x e` or
    `Decl x e`. -/
def BigNodeWritesback (g : BigCFG) (n : BigNodeID) (x : String) (e : Expr) : Prop :=
  g.nodeKind n = some .EExit ∧
  ∃ m_s m_e,
    (g.nodeKind m_s = some (.SEntry (.Assign x e)) ∨
     g.nodeKind m_s = some (.SEntry (.Decl x e))) ∧
    g.nodeKind m_e = some (.EEntry e) ∧
    g.hasEdge m_s m_e .Normal ∧
    g.hasEdge m_e n .Normal

/-- `BigNodeBranches g n c`: `n` is an `EExit` whose enclosing statement
    branches on the guard `c` — either `If c _ _` or `While c _`. -/
def BigNodeBranches (g : BigCFG) (n : BigNodeID) (c : Expr) : Prop :=
  g.nodeKind n = some .EExit ∧
  ∃ m_s m_e,
    ((∃ t f, g.nodeKind m_s = some (.SEntry (.If c t f))) ∨
     (∃ b,   g.nodeKind m_s = some (.SEntry (.While c b)))) ∧
    g.nodeKind m_e = some (.EEntry c) ∧
    g.hasEdge m_s m_e .Normal ∧
    g.hasEdge m_e n .Normal

/-! ## `BigStepN`

A single CEK `Step` paired with a CFG-level move, classified by the
shape of the move.
-/
inductive BigStepN (g : BigCFG) :
    {n : Nat} → n < g.nodes.length → CEK →
    {n' : Nat} → n' < g.nodes.length → CEK → Prop where
  /-- One CEK step, no CFG move, env preserved. Used for
      expression-evaluation steps and structural reframings
      (`.SeqEnter`, `.WhileD`, `.WhileC`, …). -/
  | stutter {n : Nat} (h : n < g.nodes.length) {σ σ' : CEK} :
      Step σ σ' →
      σ'.E = σ.E →
      BigStepN g h σ h σ'
  /-- Writeback step: `Step.AssignD` / `Step.DeclD`. The source is an
      `EExit` paired with an upstream `Assign`/`Decl` SEntry. -/
  | mutate {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
      {σ σ' : CEK} (x : String) (e : Expr) (v : Val) :
      Step σ σ' →
      BigNodeWritesback g n x e →
      EvalExpr σ.E e v →
      g.hasEdge n n' .Normal →
      σ'.E = σ.E.updated x v →
      BigStepN g h σ h' σ'
  /-- Guard-step: `Step.IfT` / `Step.IfF` / `Step.WhileT` / `Step.WhileF`.
      The source is an `EExit` of an `If` / `While` guard. -/
  | branch {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
      {σ σ' : CEK} (c : Expr) (k : EdgeKind) (v : Val) :
      Step σ σ' →
      BigNodeBranches g n c →
      g.hasEdge n n' k →
      EvalExpr σ.E c v →
      BranchTaken k v →
      σ'.E = σ.E →
      BigStepN g h σ h' σ'
  /-- Generic env-preserving CFG advance along a `Normal` edge. Captures
      `SEntry s → EEntry e` (`.Assign`/`.Decl`/`.IfC`/`.WhileC`) and
      `SExit s₁ → SEntry s₂` (`.SeqMid`). -/
  | advance {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
      {σ σ' : CEK} :
      Step σ σ' →
      g.hasEdge n n' .Normal →
      σ'.E = σ.E →
      BigStepN g h σ h' σ'

theorem BigStepN.toStep {g : BigCFG}
    {n n' : Nat} {h : n < g.nodes.length} {h' : n' < g.nodes.length}
    {σ σ' : CEK} (hsim : BigStepN g h σ h' σ') : Step σ σ' := by
  cases hsim with
  | stutter _ hstep _ => exact hstep
  | mutate _ _ _ _ _ hstep _ _ _ _ => exact hstep
  | branch _ _ _ _ _ hstep _ _ _ _ _ => exact hstep
  | advance _ _ hstep _ _ => exact hstep

/-! ## `BigStepsN` — RTC with structural `skipBridge` -/
inductive BigStepsN (g : BigCFG) :
    {n : Nat} → n < g.nodes.length → CEK →
    {n' : Nat} → n' < g.nodes.length → CEK → Prop where
  | refl {n : Nat} (h : n < g.nodes.length) (σ : CEK) :
      BigStepsN g h σ h σ
  | step {n n₁ n' : Nat}
      (h : n < g.nodes.length) (h₁ : n₁ < g.nodes.length)
      (h' : n' < g.nodes.length) {σ σ₁ σ' : CEK} :
      BigStepN g h σ h₁ σ₁ → BigStepsN g h₁ σ₁ h' σ' →
      BigStepsN g h σ h' σ'
  /-- Zero-CEK-step structural bridge along a `Normal` edge. Source and
      destination are not constrained beyond the edge — the legitimate
      cases (`EEntry → EExit`, while back-edge, if-merges) all share the
      shape "post-stutter source CEK already matches destination". -/
  | skipBridge {n n₁ n' : Nat}
      (h : n < g.nodes.length) (h₁ : n₁ < g.nodes.length)
      (h' : n' < g.nodes.length) {σ σ' : CEK} :
      g.hasEdge n n₁ .Normal →
      BigStepsN g h₁ σ h' σ' →
      BigStepsN g h σ h' σ'

/-- Lift a single `BigStepN` to a `BigStepsN`. -/
def BigStepsN.single {g : BigCFG} {n n' : Nat}
    (h : n < g.nodes.length) (h' : n' < g.nodes.length)
    {σ σ' : CEK} (hsn : BigStepN g h σ h' σ') : BigStepsN g h σ h' σ' :=
  .step h h' h' hsn (.refl h' σ')

theorem BigStepsN.trans {g : BigCFG}
    {n n₁ n' : Nat}
    {h : n < g.nodes.length} {h₁ : n₁ < g.nodes.length}
    {h' : n' < g.nodes.length} {σ σ₁ σ' : CEK}
    (hl : BigStepsN g h σ h₁ σ₁) (hr : BigStepsN g h₁ σ₁ h' σ') :
    BigStepsN g h σ h' σ' := by
  induction hl with
  | refl _ _ => exact hr
  | step h _ _ hsn _ ih =>
    exact .step h _ h' hsn (ih hr)
  | skipBridge h _ _ hedge _ ih =>
    exact .skipBridge h _ h' hedge (ih hr)

/-- A `BigCFG` state is `IsInitial` if its env is empty and its
    continuation stack is empty. Same definition as the regular case;
    we duplicate it to keep `Big` self-contained. -/
def IsInitial (_ : BigCFG) (σ : CEK) : Prop :=
  σ.E = State.empty ∧ σ.K = []

end Flow.Eval.Big.Refinement

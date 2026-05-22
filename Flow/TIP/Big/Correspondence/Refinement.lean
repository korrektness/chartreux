import Flow.TIP.Big.CFG
import Flow.TIP.Eval
import Flow.TIP.Regular.Correspondence.Refinement

namespace Flow.Eval.Big.Refinement

def BranchTaken : EdgeKind -> Val -> Prop
| .TBranch, .Int n => n ≠ 0
| .FBranch, .Int 0 => True
| _,        _       => False

def BigNodeWritesback (g : BigCFG) (n : BigNodeID) (x : String) (e : Expr) : Prop :=
  g.nodeKind n = some .EExit ∧
  ∃ m_s m_e,
    (g.nodeKind m_s = some (.SEntry (.Assign x e)) ∨
     g.nodeKind m_s = some (.SEntry (.Decl x e))) ∧
    g.nodeKind m_e = some (.EEntry e) ∧
    g.hasEdge m_s m_e .Normal ∧
    g.hasEdge m_e n .Normal

def BigNodeBranches (g : BigCFG) (n : BigNodeID) (c : Expr) : Prop :=
  g.nodeKind n = some .EExit ∧
  ∃ m_s m_e,
    ((∃ t f, g.nodeKind m_s = some (.SEntry (.If c t f))) ∨
     (∃ b,   g.nodeKind m_s = some (.SEntry (.While c b)))) ∧
    g.nodeKind m_e = some (.EEntry c) ∧
    g.hasEdge m_s m_e .Normal ∧
    g.hasEdge m_e n .Normal

inductive BigStepN (g : BigCFG) :
    {n : Nat} -> n < g.nodes.length -> CEK ->
    {n' : Nat} -> n' < g.nodes.length -> CEK -> Prop where
  -- cek steps without changing the cfg
  | stutter {n : Nat} (h : n < g.nodes.length) {σ σ' : CEK} :
      Step σ σ' ->
      σ'.E = σ.E ->
      BigStepN g h σ h σ'
  -- cek steps edits E in a way that corresponds to what the CFG expected
  | mutate {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
      {σ σ' : CEK} (x : String) (e : Expr) (v : Val) :
      Step σ σ' ->
      BigNodeWritesback g n' x e ->
      EvalExpr σ.E e v ->
      g.hasEdge n n' .Normal ->
      σ'.E = σ.E.updated x v ->
      BigStepN g h σ h' σ'
  -- step that takes a particular branch
  | branch {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
      {σ σ' : CEK} (c : Expr) (k : EdgeKind) (v : Val) :
      Step σ σ' ->
      BigNodeBranches g n c ->
      g.hasEdge n n' k ->
      EvalExpr σ.E c v ->
      BranchTaken k v ->
      σ'.E = σ.E ->
      BigStepN g h σ h' σ'
  -- cek steps by following a regular edge
  | advance {n n' : Nat} (h : n < g.nodes.length) (h' : n' < g.nodes.length)
      {σ σ' : CEK} :
      Step σ σ' ->
      g.hasEdge n n' .Normal ->
      σ'.E = σ.E ->
      BigStepN g h σ h' σ'

theorem BigStepN.toStep {g : BigCFG}
    {n n' : Nat} {h : n < g.nodes.length} {h' : n' < g.nodes.length}
    {σ σ' : CEK} (hsim : BigStepN g h σ h' σ') : Step σ σ' := by
  cases hsim with
  | stutter _ hstep _ => exact hstep
  | mutate _ _ _ _ _ hstep _ _ _ _ => exact hstep
  | branch _ _ _ _ _ hstep _ _ _ _ _ => exact hstep
  | advance _ _ hstep _ _ => exact hstep

inductive BigStepsN (g : BigCFG) :
    {n : Nat} -> n < g.nodes.length -> CEK ->
    {n' : Nat} -> n' < g.nodes.length -> CEK -> Prop where
  | refl {n : Nat} (h : n < g.nodes.length) (σ : CEK) :
      BigStepsN g h σ h σ
  | step {n n₁ n' : Nat}
      (h : n < g.nodes.length) (h₁ : n₁ < g.nodes.length)
      (h' : n' < g.nodes.length) {σ σ₁ σ' : CEK} :
      BigStepN g h σ h₁ σ₁ -> BigStepsN g h₁ σ₁ h' σ' ->
      BigStepsN g h σ h' σ'
  -- cfg steps without cek being stepped.
  | skipBridge {n n₁ n' : Nat}
      (h : n < g.nodes.length) (h₁ : n₁ < g.nodes.length)
      (h' : n' < g.nodes.length) {σ σ' : CEK} :
      g.hasEdge n n₁ .Normal ->
      BigStepsN g h₁ σ h' σ' ->
      BigStepsN g h σ h' σ'

def BigStepsN.single {g : BigCFG} {n n' : Nat}
    (h : n < g.nodes.length) (h' : n' < g.nodes.length)
    {σ σ' : CEK} (hsn : BigStepN g h σ h' σ') : BigStepsN g h σ h' σ' :=
  .step h h' h' hsn (.refl h' σ')

theorem BigStepsN.trans {g : BigCFG} {n n₁ n' : Nat}
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

def IsInitial (_ : BigCFG) (σ : CEK) : Prop := σ.IsInitial

end Flow.Eval.Big.Refinement

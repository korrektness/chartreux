import Flow.Lang.CFG
import Flow.Eval.LangEval

def CFG.hasEdge (g : CFG) (src dst : Nat) (lbl : EdgeKind) : Prop :=
  ⟨src, dst, lbl⟩ ∈ g.edges

inductive CFGStep (g : CFG) : Nat -> State -> Nat -> State -> Prop where
| assign :
    g.nodeKind n = some (.assign x e) -> EvalExpr σ e v σ' ->
    g.hasEdge n n' .normal ->
    CFGStep g n σ n' (σ'.updated x v)
| decl :
    g.nodeKind n = some (.varDecl _) ->
    g.hasEdge n n' .normal ->
    CFGStep g n σ n' σ
| entry :
    g.nodeKind n = some .entry →
    g.hasEdge n n' .normal →
    CFGStep g n σ n' σ
| exit :
    g.nodeKind n = some .exit →
    g.hasEdge n n' .normal →
    CFGStep g n σ n' σ
| cond_true :
    g.nodeKind n = some (.cond c) ->
    EvalExpr σ e (.Int k) σ' -> k ≠ 0 ->
    g.hasEdge n n' .trueBranch ->
    CFGStep g n σ n' σ'
| cond_false :
    g.nodeKind n = some (.cond c) ->
    EvalExpr σ e (.Int 0) σ' ->
    g.hasEdge n n' .falseBranch ->
    CFGStep g n σ n' σ'

inductive CFGSteps (g : CFG) : NodeId → State → NodeId → State → Prop where
  | refl :
      CFGSteps g n σ n σ
  | step :
      CFGStep g n σ n' σ' → CFGSteps g n' σ' n'' σ'' →
      CFGSteps g n σ n'' σ''

def Reachable (g : CFG) (σ : State) (n : Nat) (σ' : State) : Prop :=
    CFGSteps g g.entry σ n σ'

theorem CFGSteps.trans (h₁ : CFGSteps g n₁ σ₁ n₂ σ₂) (h₂ : CFGSteps g n₂ σ₂ n₃ σ₃) :
    CFGSteps g n₁ σ₁ n₃ σ₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem CFGSteps.single (h : CFGStep g n σ n' σ') : CFGSteps g n σ n' σ' :=
  .step h .refl

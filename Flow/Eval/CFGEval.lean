import Flow.Lang.BigCFG
import Flow.Lang.Eval

structure CE where
  id : Nat
  E  : State
  S  : List Val

inductive Silent : NodeKind -> Prop where
| entry        : Silent .entry
| stmtEntry s  : Silent (.stmtEntry s)
| stmtExitSkip : Silent (.stmtExit .Skip)
| stmtExitSeq  : Silent (.stmtExit (.Seq s₁ s₂))
| stmtExitIf   : Silent (.stmtExit (.If c t e))
| stmtExitWhile: Silent (.stmtExit (.While c b))
| exprEntry e  : Silent (.exprEntry e)

inductive CFGStep (g : BigCFG) : CE -> CE -> Prop where
| pass :
    g.nodeKind src = some kind ->
    Silent kind ->
    g.hasEdge src dst .normal ->
    CFGStep g ⟨src, E, S⟩ ⟨dst, E, S⟩
| literal :
    g.nodeKind src = some (.literal v) ->
    g.hasEdge src dst .normal ->
    CFGStep g ⟨src, E, S⟩ ⟨dst, E, v :: S⟩
| varExit :
    g.nodeKind src = some (.exprExit (.Var x)) ->
    E x = some v ->
    g.hasEdge src dst .normal ->
    CFGStep g ⟨src, E, S⟩ ⟨dst, E, v :: S⟩
| binopExit :
    g.nodeKind src = some (.exprExit (.BinOp o e₁ e₂)) ->
    g.hasEdge src dst .normal ->
    CFGStep g ⟨src, E, .Int n₂ :: .Int n₁ :: S⟩
              ⟨dst, E, .Int (applyOp o n₁ n₂) :: S⟩
-- | condT :
--     g.nodeKind src = some (.cond c) ->
--     n ≠ 0 ->
--     g.hasEdge src dst .trueBranch ->
--     CFGStep g ⟨src, E, .Int n :: S⟩ ⟨dst, E, S⟩
-- | condF :
--     g.nodeKind src = some (.cond c) ->
--     g.hasEdge src dst .falseBranch ->
--     CFGStep g ⟨src, E, .Int 0 :: S⟩ ⟨dst, E, S⟩
| declExit :
    g.nodeKind src = some (.stmtExit (.Decl x e)) ->
    g.hasEdge src dst .normal ->
    CFGStep g ⟨src, E, v :: S⟩ ⟨dst, E.updated x v, S⟩
| assignExit :
    g.nodeKind src = some (.stmtExit (.Assign x e)) ->
    g.hasEdge src dst .normal ->
    CFGStep g ⟨src, E, v :: S⟩ ⟨dst, E.updated x v, S⟩

inductive CFGSteps (g : BigCFG) : CE -> CE -> Prop where
| refl : CFGSteps g σ σ
| step : CFGStep g σ σ' -> CFGSteps g σ' σ'' -> CFGSteps g σ σ''

def CFGSteps.trans {g} (hl : CFGSteps g σ σ') (hr : CFGSteps g σ' σ'') :
    CFGSteps g σ σ'' := by
  induction hl with
  | refl => assumption
  | step hstep _ ih => exact .step hstep (ih hr)

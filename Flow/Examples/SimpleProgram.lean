import Flow.Lang.Defs
import Flow.Lang.CFG
import Flow.Analysis.CP
import Flow.Lang.BuildSpec
import Flow.Utils.DotPrinter

open Flow.Analysis Flow.Analysis.CP Flow.Lang Flow.Analysis.Generic

open Expr Stmt BinOp

def simple :=
  Seq (Decl "a" (.Int 0))
    (Seq (Decl "b" (.Int 1))
      (If (BinOp gt (Var "n") (.Int 0))
        (Assign "b" (BinOp add (Var "a") (Var "b")))
        (Assign "b" (BinOp add (Var "b") (Var "b")))))

def simpleCFG : CFG :=
  let (b, (entry, exit)) := CFGBuilder.empty.buildGraph simple
  { b.cfg with entry, exit }

def sv := varsInProgram simpleCFG
-- to refactor out: shouldn't need to carry this around
lemma sv_nodup : sv.Nodup := eraseDups_nodup sv

-- to refactor out: these proofs should work for all CFGs so shouldn't need to
-- have it around.
private lemma sv_edges_wf : ∀ {e} {_ : e ∈ simpleCFG.edges},
  e.src < simpleCFG.nodes.length := by decide
def sv_CFG := forCFG simpleCFG (by {
  intro n e he
  apply sv_edges_wf
  grind [inEdges]
})

def res := runDataflow sv_CFG (cpTransfer sv simpleCFG)
    (cpEdgeTransfer sv)
    (cpEntryInit sv)

def rd := fun n =>
    if h : n ∈ sv_CFG.nodes then res.1 ⟨n, h⟩
    else (fun _ => CPVal.bot)

lemma rd_postfix :
    PostFixpoint (cpDFA sv) cpAbsorbs simpleCFG rd := by
  intro n n' hn hn' ⟨k, hedge⟩
  unfold CFG.hasEdge at hedge
  simp only [cpAbsorbs]
  have hedges : simpleCFG.edges =
      [⟨2,3,.TBranch⟩, ⟨2,4,.FBranch⟩, ⟨3,5,.Normal⟩,
       ⟨4,5,.Normal⟩, ⟨1,2,.Normal⟩, ⟨0,1,.Normal⟩] := by decide
  rw [hedges] at hedge
  clear hedges
  simp only [List.mem_cons, Edge.mk.injEq, List.not_mem_nil, or_false] at hedge
  rcases hedge
    with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  all_goals native_decide -- sheesh

theorem cp_correct
    {n n' : Nat}
    {h : n < simpleCFG.nodes.length} {h' : n' < simpleCFG.nodes.length}
    {σ σ'}
    (hsteps : Flow.Eval.Refinement.StepsN simpleCFG h σ h' σ')
    (hcorr : cpβ_corr simpleCFG (rd n) σ) :
    cpβ_corr simpleCFG (rd n') σ' :=
  Flow.Analysis.CP.soundness sv_nodup rd_postfix hsteps hcorr

#eval IO.println (CFG.toDot simpleCFG)
#eval IO.println (CFG.toDotWith simpleCFG sv_CFG res.1 res.2)

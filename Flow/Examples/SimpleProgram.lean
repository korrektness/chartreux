import Flow.Lang.Defs
import Flow.Lang.CFG
import Flow.Analysis.CP
import Flow.Analysis.WorklistProofs
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

def rd : NodeID → CPFact sv := fun n =>
    if h : n ∈ sv_CFG.nodes then
      expectedIn sv_CFG (cpEdgeTransfer sv) (cpEntryInit sv) res.2 ⟨n, h⟩
    else (fun _ => CPVal.bot)

private lemma simpleCFG_no_entry_edge :
    ∀ e ∈ simpleCFG.edges, e.dst ≠ simpleCFG.entry := by decide

private lemma sv_CFG_hpost :
    IsForwardPostFixpoint sv_CFG (cpTransfer sv simpleCFG) (cpEdgeTransfer sv)
      (cpEntryInit sv) res.2 :=
  worklistForward_sound_postfixpoint sv_CFG (cpTransfer sv simpleCFG)
    (cpEdgeTransfer sv) (cpEntryInit sv) (fun _ => ⊥) sv_CFG.nodes_mem
    (by intro m hm; exact absurd (List.mem_attach _ m) hm)

lemma rd_postfix :
    PostFixpoint (cpDFA sv) cpAbsorbs simpleCFG rd :=
  postFixpoint_of_isForwardPostFixpoint
    (g := simpleCFG) (G := sv_CFG)
    (hnodes  := by
      intro n; simp [sv_CFG, forCFG, List.mem_range])
    (hedges  := rfl) (hentry := rfl) (hsrcOf := fun _ => rfl)
    (hinEdges := by
      intro n e
      simp [sv_CFG, forCFG, inEdges, List.mem_filter])
    (nodeTransfer := cpTransfer sv simpleCFG)
    (edgeTransfer := cpEdgeTransfer sv)
    (entryInit := cpEntryInit sv) (outF := res.2)
    (hpost := sv_CFG_hpost)
    (hno_entry_edge := simpleCFG_no_entry_edge)

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

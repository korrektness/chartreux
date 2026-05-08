import Flow.Lang.Defs
import Flow.Lang.CFG
import Flow.Analysis.CP
import Flow.Analysis.WorklistProofs
import Flow.Utils.DotPrinter

open Flow.Analysis Flow.Analysis.CP Flow.Analysis.Generic CFGBuilder Flow.Eval.Refinement

section Simple
open Expr Stmt BinOp in
def simple :=
  Seq (Decl "a" (.Int 0))
    (Seq (Decl "b" (.Int 1))
      (If (BinOp gt (Var "n") (.Int 0))
        (Assign "b" (BinOp add (Var "a") (Var "b")))
        (Assign "b" (BinOp add (Var "b") (Var "b")))))

def simpleCFG : CFG :=
  let (b, (entry, exit)) := CFGBuilder.empty.buildGraphTuple simple
  { b.cfg with entry, exit }

def sv := simpleCFG.vars

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
    (hsteps : StepsN simpleCFG h σ h' σ')
    (hcorr : cpβ_corr simpleCFG (rd n) σ) :
    cpβ_corr simpleCFG (rd n') σ' :=
  soundness sv.prop rd_postfix hsteps hcorr

private lemma rd_entry_absorb :
    cpAbsorbs (cpEntryInit sv) (rd simpleCFG.entry) := by
  simp only [cpAbsorbs]
  decide

theorem cp_correct_reachable
    {n : Nat} {h : n < simpleCFG.nodes.length} {σ : CEK}
    (hreach : Reachable simpleCFG h σ) :
    cpβ_corr simpleCFG (rd n) σ :=
  reachable_corr (cpSemantics sv sv.prop) (@mono_absorb_cp sv)
    rd_postfix rd_entry_absorb hreach

#eval IO.println (CFG.toDot simpleCFG)
#eval IO.println (CFG.toDotWith simpleCFG sv_CFG res.1 res.2)
end Simple

section Hard
open Expr Stmt BinOp in
/-- The example program. -/
def loopy : Stmt :=
  Seq (Decl "x" (.Int 2))
    (Seq (Decl "y" (.Int 3))
      (Seq (Decl "i" (.Int 0))
        (Seq (Decl "z" (.Int 0))
          (While (BinOp gt (Var "n") (Var "i"))
            (Seq (Assign "i" (BinOp add (Var "i") (.Int 1)))
                 (If (BinOp gt (Var "x") (.Int 0))
                   (Assign "z" (BinOp mul (Var "x") (Var "y")))
                   (Assign "z" (BinOp mul (Var "y") (Var "x")))))))))

def loopyCFG : CFG := CFG.ofStmt loopy

private lemma loopyCFG_wf : loopyCFG.WellFormed := by decide

def loopyVars : { l : List String // l.Nodup } := loopyCFG.vars

def loopyResult :
    Flow.AnalysisResult (cpAnalysis loopyVars.val loopyVars.prop) loopyCFG :=
  Flow.analyze (cpAnalysis loopyVars.val loopyVars.prop) loopyCFG loopyCFG_wf

theorem loopy_cp_correct
    {n : Nat} {h : n < loopyCFG.nodes.length} {σ : CEK}
    (hreach : Reachable loopyCFG h σ) :
    cpβ_corr loopyCFG (loopyResult.inFacts n) σ :=
  cp_reachable_correct loopyVars.prop loopyCFG_wf hreach

#eval IO.println (CFG.toDot loopyCFG)
#eval IO.println (CFG.toDotWithFn (A := CPFact loopyVars.val) loopyCFG
  loopyResult.inFacts loopyResult.outFacts)
end Hard

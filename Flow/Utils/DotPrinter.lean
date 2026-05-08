import Flow.Lang.Defs
import Flow.Lang.CFG
import Flow.Analysis.Lattice

/-! # DOT (Graphviz) printer for `CFG`

This module provides a small utility to render a `CFG` as a Graphviz DOT
string, optionally overlaid with the IN/OUT facts of a dataflow analysis
(supplied as a pair of `StateN`s).
-/

namespace Flow.Utils.DotPrinter

/-! ## String escaping and pretty-printers -/

/-- Escape a string for embedding inside a DOT double-quoted label.
    Backslashes and double-quotes are escaped; newlines become the DOT
    left-justify marker `\l`. -/
private def escapeDot (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\"
    | '"'  => acc ++ "\\\""
    | '\n' => acc ++ "\\l"
    | _    => acc.push c

private def BinOp.toStr : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .gt  => ">"
  | .eq  => "=="

private def Expr.toStr : Expr → String
  | .Int n      => toString n
  | .Var x      => x
  | .BinOp o a b => "(" ++ Expr.toStr a ++ " " ++ BinOp.toStr o ++ " " ++ Expr.toStr b ++ ")"

private def NodeKind.toStr : NodeKind → String
  | .Assign x e => x ++ " := " ++ Expr.toStr e
  | .Decl   x e => "var " ++ x ++ " := " ++ Expr.toStr e
  | .Cond   c   => "if " ++ Expr.toStr c
  | .Skip       => "skip"

/-- DOT attribute fragment for an `EdgeKind`. -/
private def EdgeKind.attrs : EdgeKind → String
  | .Normal  => ""
  | .TBranch => "label=\"T\",color=darkgreen"
  | .FBranch => "label=\"F\",color=red"

/-! ## Annotator and core printer -/

/-- An optional per-node annotation: given a `NodeID`, returns
    `some (in, out)` strings to overlay on the node label, or `none` to
    leave the label bare. -/
abbrev Annotator := NodeID → Option (String × String)

private def renderNode (entry exit : NodeID) (annot : Annotator)
    (id : NodeID) (k : NodeKind) : String :=
  let isInternalSkip := k = .Skip ∧ id ≠ entry ∧ id ≠ exit
  let body := if isInternalSkip then "" else toString id ++ ": " ++ NodeKind.toStr k
  let label :=
    if isInternalSkip then
      ""
    else
      match annot id with
      | some (i, o) =>
        "IN: " ++ i ++ "\n" ++ body ++ "\n" ++ "OUT: " ++ o ++ "\n"
      | none => body
  let escaped := escapeDot label
  let baseAttrs := "label=\"" ++ escaped ++ "\""
  let withSkip :=
    if isInternalSkip then
      baseAttrs ++ ",shape=box,width=0.2,height=0.2,fixedsize=true"
    else
      baseAttrs
  let withEntry := if id = entry then withSkip ++ ",style=bold" else withSkip
  let attrs := if id = exit then withEntry ++ ",shape=doubleoctagon" else withEntry
  "  n" ++ toString id ++ " [" ++ attrs ++ "];"

private def renderEdge (e : Edge) : String :=
  let base := "  n" ++ toString e.src ++ " -> n" ++ toString e.dst
  match EdgeKind.attrs e.kind with
  | "" => base ++ ";"
  | a  => base ++ " [" ++ a ++ "];"

/-- Core DOT printer, parameterized by an optional per-node annotator. -/
private def toDotCore (g : CFG) (annot : Annotator) : String :=
  let nodeLines : List String :=
    g.nodes.zipIdx.map (fun (k, i) => renderNode g.entry g.exit annot i k)
  let edgeLines : List String := g.edges.map renderEdge
  let body := String.intercalate "\n" (nodeLines ++ edgeLines)
  "digraph CFG {\n  rankdir=TB;\n" ++ body ++ "\n}"

end Flow.Utils.DotPrinter

/-! ## Public entry points on `CFG`. -/

namespace CFG

/-- Render a `CFG` as a Graphviz DOT string with no analysis overlay. -/
def toDot (g : CFG) : String :=
  Flow.Utils.DotPrinter.toDotCore g (fun _ => none)

private def annotatorOfStates {A : Type} [ToString A]
    (ag : AnalysisCFG NodeID Edge)
    (inSt outSt : StateN ag A) :
    Flow.Utils.DotPrinter.Annotator :=
  fun n =>
    if h : n ∈ ag.nodes then
      some (toString (inSt ⟨n, h⟩), toString (outSt ⟨n, h⟩))
    else
      none

/-- Render a `CFG` as a Graphviz DOT string, overlaying each node with
    the IN/OUT facts produced by an analysis on `ag`. Nodes not present
    in `ag` fall back to the bare label. -/
def toDotWith {A : Type} [ToString A]
    (g : CFG)
    (ag : AnalysisCFG NodeID Edge)
    (inSt outSt : StateN ag A) : String :=
  Flow.Utils.DotPrinter.toDotCore g (annotatorOfStates ag inSt outSt)

end CFG

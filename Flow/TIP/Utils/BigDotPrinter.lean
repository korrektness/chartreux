import Flow.TIP.Defs
import Flow.TIP.Big.CFG

/-! # DOT printer for `BigCFG` -/

namespace Flow.Utils.BigDotPrinter

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

private def Stmt.toStr : Stmt -> String
| .Assign x e => x ++ " := " ++ Expr.toStr e
| .Decl   x e => "var x " ++ x ++ " := " ++ Expr.toStr e
| .Seq _ _    => "seq"
| .Skip       => "skip"
| .While c _  => "while " ++ Expr.toStr c
| .If c _ _   => "if " ++ Expr.toStr c

private def BigNodeKind.toStr : BigNodeKind → String
| .SEntry s => "sen: " ++ Stmt.toStr s
| .SExit    => "sex"
| .EEntry e => "een: " ++ Expr.toStr e
| .EExit    => "eex"

private def EdgeKind.attrs : EdgeKind → String
| .Normal  => ""
| .TBranch => "label=\"T\",color=darkgreen"
| .FBranch => "label=\"F\",color=red"

private def renderBigNode (entry exit : BigNodeID)
    (id : BigNodeID) (k : BigNodeKind) : String :=
  let body := toString id ++ ": " ++ BigNodeKind.toStr k
  let escaped := escapeDot body
  let baseAttrs := "label=\"" ++ escaped ++ "\""
  let withEntry := if id = entry then baseAttrs ++ ",style=bold" else baseAttrs
  let attrs := if id = exit then withEntry ++ ",shape=doubleoctagon" else withEntry
  "  n" ++ toString id ++ " [" ++ attrs ++ "];"

private def renderEdge (e : Edge) : String :=
  let base := "  n" ++ toString e.src ++ " -> n" ++ toString e.dst
  match EdgeKind.attrs e.kind with
  | "" => base ++ ";"
  | a  => base ++ " [" ++ a ++ "];"

private def toDotCore (g : BigCFG) : String :=
  let nodeLines : List String := g.nodes.zipIdx.map (fun (k, i) => renderBigNode g.entry g.exit i k)
  let edgeLines : List String := g.edges.map renderEdge
  let body := String.intercalate "\n" (nodeLines ++ edgeLines)
  "digraph BigCFG {\n  rankdir=TB;\n" ++ body ++ "\n}"

private def renderBigNodeWithAnnotation (entry exit : BigNodeID)
    (id : BigNodeID) (k : BigNodeKind) (annotation : Option (String × String)) : String :=
  let body := toString id ++ ": " ++ BigNodeKind.toStr k
  let withAnnotation := match annotation with
    | some (inFact, outFact) =>
        body ++ "\nIN: " ++ inFact ++ "\nOUT: " ++ outFact
    | none => body
  let escaped := escapeDot withAnnotation
  let baseAttrs := "label=\"" ++ escaped ++ "\""
  let withEntry := if id = entry then baseAttrs ++ ",style=bold" else baseAttrs
  let attrs := if id = exit then withEntry ++ ",shape=doubleoctagon" else withEntry
  "  n" ++ toString id ++ " [" ++ attrs ++ "];"

/-- Type for an annotation function: maps node IDs to optional IN/OUT pairs. -/
private def Annotator := BigNodeID → Option (String × String)

private def toDotCoreWithAnnotator (g : BigCFG) (ann : Annotator) : String :=
  let nodeLines : List String := g.nodes.zipIdx.map (fun (k, i) =>
    renderBigNodeWithAnnotation g.entry g.exit i k (ann i))
  let edgeLines : List String := g.edges.map renderEdge
  let body := String.intercalate "\n" (nodeLines ++ edgeLines)
  "digraph BigCFG {\n  rankdir=TB;\n" ++ body ++ "\n}"

end Flow.Utils.BigDotPrinter

namespace BigCFG

def toDot (g : BigCFG) : String :=
  Flow.Utils.BigDotPrinter.toDotCore g

/-- Render a `BigCFG` as a Graphviz DOT string, overlaying each node with
    the IN/OUT facts produced by an analysis. The annotator function maps
    each node ID to optional IN/OUT pairs. -/
def toDotWithFn {A : Type} [ToString A]
    (g : BigCFG) (inF outF : BigNodeID → A) : String :=
  Flow.Utils.BigDotPrinter.toDotCoreWithAnnotator g
    (fun n => some (toString (inF n), toString (outF n)))

end BigCFG

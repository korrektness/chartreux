import Chartreux.Duke.CFG
import Chartreux.Duke.Defs
import Chartreux.Duke.Resolve

namespace List

variable {α : Type} (x : α) (l : List α)
variable [DecidableEq α]

theorem finIdxOf?_nodup (hnd : l.Nodup)
    (i j : Fin l.length) (hi : l.finIdxOf? x = some i) (hneq : j ≠ i) :
    x ≠ l.get j := by
  intro h_eq
  have hget := List.finIdxOf?_eq_some_iff.mp hi |>.left
  subst h_eq
  rw [List.get_eq_getElem] at *
  have := (List.getElem_inj hnd).1 hget
  grind

end List


variable (mapping : Mapping)

-- # DotPrinter (sanity check)
namespace Dot

def binOpStr : BinOp -> String
| .add => "+"
| .sub => "-"
| .mul => "*"
| .lt  => "<"
| .eq  => "=="
| .and => "&&"

partial def exprStr : NExpr -> String
| .Null            => "null"
| .Int n           => toString n
| .Var x           => mapping.get x
| .IsNull e        => s!"isnull({exprStr e})"
| .Not e           => s!"!({exprStr e})"
| .BinOp o e₁ e₂   => s!"({exprStr e₁} {binOpStr o} {exprStr e₂})"

def nodeLabel : NodeKind -> String
| .Skip               => "skip"
| .Declare x none     => s!"let {mapping.get x}"
| .Declare x (some e) => s!"let {mapping.get x} := {exprStr mapping e}"
| .Assign x e         => s!"{mapping.get x} := {exprStr mapping e}"
| .Assume e           => s!"assume {exprStr mapping e}"
| .BlockEnter         => s!"BlockEnter"
| .BlockExit          => s!"BlockExit"

-- escape characters that are special inside a Graphviz quoted label.
def escape (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
            | '"'  => "\\\""
            | '\\' => "\\\\"
            | '\n' => "\\l"
            | _    => String.singleton c)) ""

def shape : NodeKind -> String
| .Assume _ => "ellipse"
| _         => "box"

-- Annotations
abbrev Annotator := NodeID -> Option (String × String)

def nodeText (annot : Annotator) (i : NodeID) (k : NodeKind) : String :=
  let body := s!"{i}: {nodeLabel mapping k}"
  match annot i with
  | some (inS, outS) => s!"IN: {inS}\n{body}\nOUT: {outS}\n"
  | none             => body

/-- Core DOT printer, parameterized by an optional per-node annotator. -/
def toDotCore (g : CFG) (annot : Annotator) : String :=
  let nodeLines :=
    g.nodes.zipIdx.map (fun (k, i) =>
      s!"  n{i} [label=\"{escape (nodeText mapping annot i k)}\", shape={shape k}];")
  let edgeLines :=
    g.edges.map (fun e => s!"  n{e.src} -> n{e.dst};")
  let body := String.intercalate "\n" (nodeLines ++ edgeLines)
  s!"digraph CFG \{\n{body}\n}"

def toDot (g : CFG) : String := toDotCore mapping g (fun _ => none)

def annotatorOfStates {A : Type} [ToString A]
    (ag : AnalysisCFG NodeID Edge) (inSt outSt : StateN ag A) : Dot.Annotator :=
  fun n =>
    if h : n ∈ ag.nodes then
      some (toString (inSt ⟨n, h⟩), toString (outSt ⟨n, h⟩))
    else
      none

end Dot

/-- annotated printing -/
def CFG.toDotWithFn {A : Type} [ToString A]
    (g : CFG) (inF outF : NodeID -> A) : String :=
  Dot.toDotCore mapping g (fun n => some (toString (inF n), toString (outF n)))

/-- unannotated printing -/
def Stmt.toDot (s : Stmt) :=
  match resolve s with
  | some (s', mapping) => Dot.toDotCore mapping s'.cfg (fun _ => none)
  | none => "???"

open Duke.Syntax

-- sanity checks
#eval IO.println (
    @let "x" := null ;;
    "x" ::= 0
  ).toDot

#eval IO.println (
    @let "x" ;;
    @if "x" @< 0 @then
      "x" ::= 1
    @else
      "x" ::= 2
  ).toDot

#eval IO.println (
    @let "x" := 2 ;;
    @let "y" := 2 ;;
    @if "x" @&& "y" @then
      "x" ::= null
    @else
      "x" ::= 1
  ).toDot

#eval IO.println (
    @let "i" := 1 ;;
    @while "i" @< 10 @do
      "i" ::= "i" + 1
  ).toDot

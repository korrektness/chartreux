import Chartreux.Duke.CFG

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


-- # DotPrinter (sanity check)
namespace Dot

def binOpStr : BinOp -> String
| .add => "+"
| .sub => "-"
| .mul => "*"
| .lt  => "<"
| .eq  => "=="
| .and => "&&"

partial def exprStr : Expr -> String
| .Null            => "null"
| .Int n           => toString n
| .Var x           => x
| .IsNull e        => s!"isnull({exprStr e})"
| .Not e           => s!"!({exprStr e})"
| .BinOp o e₁ e₂   => s!"({exprStr e₁} {binOpStr o} {exprStr e₂})"

def nodeLabel : NodeKind -> String
| .Skip       => "skip"
| .Assign x e => s!"{x} := {exprStr e}"
| .Assume e   => s!"assume {exprStr e}"

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
  let body := s!"{i}: {nodeLabel k}"
  match annot i with
  | some (inS, outS) => s!"IN: {inS}\n{body}\nOUT: {outS}\n"
  | none             => body

/-- Core DOT printer, parameterized by an optional per-node annotator. -/
def toDotCore (g : CFG) (annot : Annotator) : String :=
  let nodeLines :=
    g.nodes.zipIdx.map (fun (k, i) =>
      s!"  n{i} [label=\"{escape (nodeText annot i k)}\", shape={shape k}];")
  let edgeLines :=
    g.edges.map (fun e => s!"  n{e.src} -> n{e.dst};")
  let body := String.intercalate "\n" (nodeLines ++ edgeLines)
  s!"digraph CFG \{\n{body}\n}"

def toDot (g : CFG) : String := toDotCore g (fun _ => none)

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
  Dot.toDotCore g (fun n => some (toString (inF n), toString (outF n)))

/-- unannotated printing -/
def Stmt.toDot (s : Stmt) := Dot.toDotCore s.cfg (fun _ => none)

-- sanity checks
#eval IO.println (Stmt.Seq (Stmt.Decl "x" (.Null)) (Stmt.Assign "x" (.Int 0))).toDot

#eval IO.println
  (Stmt.If (.BinOp .lt (.Var "x") (.Int 0))
    (Stmt.Assign "x" (.Int 1))
    (Stmt.Assign "x" (.Int 2))).toDot

#eval IO.println
  (Stmt.If (.BinOp .and (.Var "x") (.Var "y"))
    (Stmt.Assign "x" (.Null))
    (Stmt.Assign "x" (.Int 1))).toDot

#eval IO.println
  (Stmt.While (.BinOp .lt (.Var "i") (.Int 10))
    (Stmt.Assign "i" (.BinOp .add (.Var "i") (.Int 1)))).toDot

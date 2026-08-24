#import "@preview/fine-lncs:0.6.5": author, institute, lncs
#import "./utils.typ": lemma, proof, setup-theorems, theorem
#import "@preview/curryst:0.6.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#show: setup-theorems

#show raw: set block(
  fill: silver.lighten(65%),
  width: 100%,
  inset: 1.5em,
  outset: -0.5em,
)

#let inst_jb = institute(
  "JetBrains München",
  email: "firstname.lastname@jetbrains.com",
)

#let auth_qtz = author(
  "Jacopo Moretti",
  insts: (inst_jb),
  oicd: "0009-0000-3662-1683",
)

#let auth_mw = author(
  "Marcin Wojnarowski",
  insts: (inst_jb),
  oicd: "0009-0003-7962-3904",
)

#let note = it => note[
  #set text(7pt)
  #set par(justify: false)
  #it
]

#show: lncs.with(
  title: "Chartreux: Towards Verified Dataflow Analyses for Kotlin",
  authors: (auth_qtz, auth_mw),
  running-author: "Moretti and Wojnarowski",
  abstract: [
    The Kotlin programming language differs from others through its use of
    dataflow analysis not just as a way to optimize the generated code, but also
    as a complement to type analysis, to decide program validity and increase
    the expressive power of the language. These analyses include flow sensitive
    type refinement of expressions ("smart casts"), and more recently, function
    contracts on lambda parameters. While useful, the implementation of these
    analyses carries no guarantees, and the soundness of their behavior is not
    immediately obvious. To aid the understanding of current analyses, and the
    design of new ones, we present Chartreux, a generic Lean framework for
    specifying and verifying dataflow analyses on control flow graphs. We
    showcase how Chartreux allows language designers to verify the correctness
    of their analyses with respect to arbitrary language properties, by applying
    it to analyses and techniques from the Kotlin compiler.
  ],
  keywords: ("Dataflow Analysis", "Program Verification", "Kotlin"),
  bibliography: bibliography("refs.bib"),
  page-config: (paper: "a4"),
)

// adjusting sizes to have more space:
#set text(size: 9.3pt)

#set text(weight: 500) // hardcoded but works
#set math.equation(numbering: none)

#let lub = $union.sq$
#let squb = $subset.eq.sq$
#let succ(G, n) = $#math.sans("succ") _(#G)(#n)$

= Introduction <sec:intro>

Static analysis is a class of techniques used to analyze programs to obtain
guarantees on their behavior without having to execute them. Foundational work
by Cousot & Cousot @Cousots developed the theory of Abstract Interpretation,
unifying many static analysis approaches under one mathematical umbrella. Today,
a practical instantiation of abstract interpretation, called dataflow analysis,
is heavily employed in many modern industrial compilers such as LLVM, GCC, or
V8.

Consider the following Kotlin program:

```kt
val a = 5
if (a + 2 == 7) {
  println("It is seven!")
} else {
  println("Oh no!")
}
```

By performing a constant propagation dataflow analysis, we learn that the
condition always holds true (and has no side-effects). Therefore, we can
eliminate the ```kt if``` statement completely reducing this program to just
```kt println("It is seven!")```. This classic analysis is an example of using
analyses to perform program optimization. But this is only one example use-case
for dataflow analyses; they are also widely used for identifying potential
runtime errors.

The Kotlin compiler leverages this latter capability significantly, relying on
dataflow analyses to help the type checker decide whether a program should be
accepted. In Kotlin, this feature is known as "smart casts" @kotlin-smart-casts.
Similar approaches are also used extensively in languages such as Typed Racket
(called "occurrence typing" @racket-occurrence-typing) and TypeScript
("narrowing" @typescript-narrowing). For instance, Kotlin accepts the following
program by feeding the type checker flow-sensitive information coming from a
nullability analysis:

```kt
fun f(x: Int?): Int {
  if (x != null) {
    // Addition works because we know `x` is not null here!
    return x + 1
  }
  return 0
}
```

But Kotlin's smart casts go far beyond such simple flow typing. It can also use
boolean variables as witnesses for nullability facts, rewrite program's control
flow graph (CFG) depending on user provided function contracts, and more.
Unfortunately in practice these analyses quickly get hairy with the introduction
of things such as mutability, aliasing, or exceptions. Without a formal
understanding of the problem, the analyses can contain subtle unsoundness
issues, leading to incorrect conclusions about program's behavior. Since Kotlin
relies on these analyses to prevent a class of runtime errors, we want to be
very sure they are indeed correct. Additionally, a formal verification serves as
a tool for surfacing these subtle edge cases.

While verifying static analyzers is not a new concept, existing tools are
ill-suited for our needs. Verasco @Verasco is a Rocq-mechanized static analyzer
for CompCert's @CompCert subset of C. It establishes the absence of runtime
errors by means of many dataflow analyses. It is however specific to that single
language and therefore not directly usable for Kotlin. On the other hand @iTree
does provide a generic formalization of abstract interpreters based on
interaction trees. Unfortunately these constructions are highly complex
requiring the user to understand monadic handling, flow combinators, and more.
We have found that existing solutions are either focused on a specific language
or too complex requiring the user to prove many obligations.


// Astrée @Astree is a C analyzer used by Airbus to prove the absence
// of runtime errors, and SootUp @SootUp is a JVM bytecode analyzing library which
// similarly allows to look for runtime errors. These language-specific analyzers
// are further generalized by tools such as LiSA @LiSA which offer a
// language-agnostic framework for performing dataflow analyses.

Motivated by our need of creating a playground for verifying Kotlin's dataflow
analyses, we present `Chartreux`: a language-agnostic framework for specifying
and verifying CFG-based analyses in Lean. We instantiate it on analyses drawn
directly from the Kotlin compiler by which we establish their soundness and
derive proper guarantees for language constructs that rely on them.

By providing a low-obligation framework for CFG-based analyses, we help the
Kotlin language team by verifying the implementation of analyses currently used
in production, as well as aid and accelerate the development of novel analyses.
By being language agnostic we allow for experiments on smaller toy languages.

Our main contributions are the following:

#[
  #set enum(numbering: "(i)")
  + a framework for describing languages and analyses in Lean, with guarantees
    of correctness of said analyses;
  + mechanized soundness proofs for two analyses that mirror Kotlin language
    constructs, namely nullability with consequents (modelling Kotlin's
    flow-sensitive typing with implications) and calls-in-place lambda
    contracts.
]

@sec:bg-kotlin
dives deep into relevant Kotlin language features which are used for
smart-casts. @sec:design presents the framework's design and implementation, as
well as showing its theoretical guarantees. In @sec:appl we validate the
framework by instantiating it on analyses drawn from the Kotlin compiler, before
commenting on related work and next steps in @sec:discuss.

// == Dataflow analysis <sec:bg-dataflow>

// The goal of static analysis is to compute information on program behavior before
// any execution has taken place; to implement one is therefore to provide a
// representation of program execution and state in tractable and suitably abstract
// ways. Our framework is built around analysis problems formulated as _monotone
// frameworks_, which we present as follows.

// Throughout this document, we define a _control flow graph_ (CFG) to be a finite,
// directed graph $G = (N, E)$ representing a given program, such that every node
// is a program point and every edge corresponds to control flow between points.
// The exact CFG shape depends on the language and analysis currently under study.
// We define

// $
//   #succ($G$, $n$) = {d | (n, d) in E}
// $
// to denote the successor function for nodes of $G$.

// Then, a monotone dataflow analysis is comprised of:
// - An information domain, represented as a bounded semilattice $(L, lub, bot)$
//   where $lub$ is commutative, associative, idempotent, and $bot$ is its identity
//   element. We induce a partial order by
//   $
//     a squb b space eq.triple space a lub b = b wide forall a, b in L.
//   $
//   An element being ordered before a different one represent information that is
//   more precise with respect to the current problem domain;
// - A local monotonic transfer function $f_n : L -> L$, where $f_n (l)$ is the
//   information resulting from the interpretation of node $n$ under information
//   $l$.

// A "solution" of this analysis is a mapping $rho : N -> L$, encoding the
// information we know at every program point. This solution $rho$ is computed by
// solving the system of inequations that arises from the graph and transfer
// functions, the post-fixpoint:

// $
//   forall n in N, forall s in #succ($G$, $n$), quad f_n (rho(n)) squb rho(s)
// $

// The canonical approach for computing a solution to these equations involves an
// iterative algorithm due to Kildall @Kildall73: since editing the state at a
// given node requires recomputing the state at all successors, this algorithm
// works by maintaining a _worklist_ of nodes left to compute, terminating when no
// nodes are left. Termination is guaranteed provided that the input semilattice
// $L$ is of finite height, i.e. it doesn't contain infinite chains.

// While $rho : N -> L$ models the abstract state, we use $sigma : S$ to denote a
// concrete state of a program execution at some node $n in N$. We wish to
// establish a connection between the result of the analysis $rho$ and the concrete
// states $sigma$, which we can express by the abstraction function
// $alpha : S -> L$. We then state the following formal definition for the
// correctness of an analysis:

// #definition[
//   We say that the result of an analysis $rho: N -> L$ is correct if, there is a
//   choice of $alpha : S -> L$ such that for every possible program state
//   $sigma : S$ at the node corresponding to it $n in N$, it is the case that
//   $
//     alpha(sigma) squb rho(n)
//   $
// ]

// Intuitively, it says that $rho$ is an approximation of $sigma$ when it is mapped
// into the information domain $L$.


= The Kotlin language <sec:bg-kotlin>

Kotlin @Kotlin is a statically typed language created and developed at
JetBrains. It is designed as a modern language for the Java Virtual Machine,
incorporating both the object oriented and functional paradigm. Kotlin powers
its most unique features by the use of dataflow analysis in the type checking
phase, yielding a flow-sensitive typing that allows writing more expressive
programs while maintaining safety.

=== Nullability analysis.
Classically, in strongly typed languages, bindings keep their type throughout
execution. This is not the case in Kotlin: a binding can be _refined_ to an
instance of a more precise type, if the control flow around it provides enough
information to do so, for example in determining the legality of accesses to
potentially nullable values. In particular, this goes beyond simple
```kt if (v != null)``` checks: the analysis builds a system of implications
that tie boolean values with the names that are impacted, in order to determine
the legality of every operation.

Consider the following program, which the Kotlin compiler automatically accepts.

```kt
fun calculateTax(cost: Double?): Double? {
  val valid = cost != null && /*1*/cost > 0.0
  /*2*/

  Telemetry.log("calculateTax_valid", valid)

  if (!valid) return null

  /*3*/
  return cost * 0.23
}
```


The function receives a cost which can potentially be ```kt null```. In `valid`
we store whether the cost is not null and strictly positive. We log `valid` and
exit early if it is ```kt false```. Finally, we compute the tax if everything
went well. There are a few interesting program points which we now elaborate on:

1. Since ```kt &&``` is short-circuiting, this point is reached only if
  ```kt cost != null``` succeeded. This means Kotlin can refine `cost` to be
  non-null and allow for the ```kt >``` comparison.
2. Kotlin creates two dataflow implications. If `valid` is ```kt true``` it
  means that ```kt cost != null && cost > 0.0``` holds. Hence, `cost` is not
  ```kt null```. On the other hand, if it is ```kt false``` we do not gain any
  information about the nullability of `cost`.
3. Since we have previously exited early on the condition of ```kt !valid``` it
  means that here ```kt valid``` is ```kt true```. Using the implication from
  the previous point Kotlin learns that `cost` cannot be ```kt null```, allowing
  us to perform the multiplication!

This system allows the user to write more complex programs while still
maintaining compiler-proven ```kt null``` safety. However, under conditions of
mutability or potential aliasing, the analysis can be rendered unsound, by the
introduction of slight mismatches between the transfer functions and the
language semantics: the correctness of this witnessing behavior is not immediate
and unique.

=== Function contracts.
Another use of dataflow analysis in the Kotlin compilation process is #emph[
  function contract checking]. In Kotlin, functions are first-class, which means
they can be passed to other functions as parameters and returned like regular
values. These lambda parameters allow the user to write code following a more
functional style, but the interaction with the pre-existing dataflow system is
not intuitive, and leads to many corner cases.

Consider the following program, where `run` is a standard library function that
takes a single function as parameter.

```kt
fun main() {
  val x: Int
  run({ x = 42 })
  println(x)
}
```

In Kotlin, ```kt { x = 42 }``` is the syntax for a parameterless (closure)
lambda with the body of ```kt x = 42```. A ```kt val``` in Kotlin denotes an
immutable binding that can be assigned to only once and cannot be used before
being initialized to some value.

Without any guarantees on the behavior of `run`, we hit two compilation errors:

+ This lambda cannot be passed because `run` might potentially call it multiple
  times, causing the variable `x` to be initialized more than once;
+ The call to `println` fails, because `run` might potentially never call the
  lambda and so `x` is never initialized.

Without specifying _how_ `run` utilizes its lambda parameter, the call behaves
as an opaque system, and the initialization analysis has nothing to latch onto
to gain information: the code cannot compile. However, now consider the
following specification for `run`.

```kt
fun run(f: () -> Unit): Unit {
  contract {
    callsInPlace(f, InvocationKind.EXACTLY_ONCE)
  }
  f()
}
```

The contract becomes part of the signature of `run` itself. Here, it specifies
that `run` calls `f` exactly once before returning, which gives the analysis
enough information to pass: we now have a guarantee that `f` initializes `x`
exactly once.

#let unk = ```kt UNKNOWN```
#let eo = ```kt EXACTLY_ONCE```
#let alo = ```kt AT_LEAST_ONCE```
#let amo = ```kt AT_MOST_ONCE```

#figure(
  caption: [Sketch of the Kotlin CFG for lambda parameters in the presence of
    contracts.
  ],
)[
  #grid(columns: (1fr, 1fr, 1fr, 1fr), gutter: 1em, align: center + horizon)[
    #image("assets/exunknown.svg")
  ][
    #image("assets/exexactly_once.svg")
  ][
    #image("assets/exat_most_once.svg")
  ][
    #image("assets/exat_least_once.svg")
  ][ #unk ][ #eo ][ #amo ][ #alo ]
]<fig:cip-cfg>

Contracts exist for lambda parameters called ```kt EXACTLY_ONCE```,
```kt AT_LEAST_ONCE``` and ```kt AT_MOST_ONCE```, as well as a default
```kt UNKNOWN``` value that falls back to the default behavior. In practice, the
analysis phase implements these checks in two different passes, working together
to compile the necessary information:

+ first, a simple dataflow analysis on function bodies checks that they respect
  the contract that's declared in the function signature;
+ at any call site, the CFG is rewritten according to rules described in
  @fig:cip-cfg, which allow the result of the call to be propagated in the local
  analysis.

The rewrites increase the precision of analysis according to the contract by
inlining the lambda bodies with edges congruous with the amount of times we can
expect the lambda to be called. The introduced edges make intuitive sense in the
Kotlin programming language, but they are far from trivial: it's not clear on
first glance why the analysis result reached after considering them would be
sound; additionally, the rewrites trust the correctness of the counting
analysis, making the machinery around them brittle. Function contracts have been
an experimental Kotlin feature since 2018, with their design being the subject
of large amounts of scrutiny and discussion.

// is this paragraph used?
While type systems have systematic ways to study their interaction with
semantics, these dataflow techniques, in the formulation they usually have in
production compilers, have not enjoyed the same level of study. Our framework
reduces this gap by obtaining proper, workable guarantees and by allowing for
specifying these analyses and relating them back to program executions.

Let us now present our framework.

= Design and implementation <sec:design>

#let coh = $sans("Coh")$
#let coh-def = $coh subset.eq L times S$
#let fhbsl = `FHBSLattice`
#let fhbsls = [`FHBSLattice`s]

Before we can return to Kotlin and the analyses that we formalized, we describe
the framework in Lean alongside the obligations that are put on the user. Once
the language designer fulfills them, she obtains a theorem on the correctness of
their analysis, a relation between the abstract state computed by the algorithm
and the concrete state arising from execution. We call this relation
"coherence", and denote it by #coh-def, where $L, S$ are the abstract and
concrete state spaces respectively. As we will see later, this coherence
relation is chosen by the user depending on her goals, this allows full
flexibility in the theorems one wants to prove, while maintaining the proof
burden to a minimal amount.

Classical abstract interpretation methods would establish a connection between
abstract and concrete states through a Galois connection: given spaces $L, S$,
one would have to determine functions $alpha : S -> L, gamma : L -> S$ to obtain
preorders on both, which encode precisely the information that the analysis
should provide. While some presentations make this more suitable for formal
methods work (like Pichardie's $gamma$-only formulation @picha2005), finding a
good $alpha, gamma$ pair requires an uncomfortable amount of backwards thinking
about the guarantees that one wishes to achieve, encoding a relation between two
spaces $S$ and $L$ as a pair of two projections instead of phrasing it directly.
#coh works exactly as that direct relation, and the framework is built around
making it easy for the user to work from this relation towards a full proof of
correctness.

The final theorem of our framework is the following.

#theorem[
  Let $g = (N, E)$ be a CFG with semantics relating states in $S$. Given:
  - an analysis $A$ with transfer functions over a bounded semilattice $L$;
  - a relation #coh-def that's preserved under semantics steps,

  The post-fixpoint $rho : N -> L$ obtained by running Kildall's algorithm on
  $g$ with transfer functions from $A$ is such that for all reachable states
  $sigma : S$ at node $n in N$, $coh(rho(n), sigma)$ holds.
] <thm:framework>

In the rest of this section we explain the most important components of the
mechanized framework in Lean, while highlighting the obligations put on a user.
We conclude it with a proof of @thm:framework, certifying the soundness of an
analysis.


== CFGs

A CFG is represented as a list of abstract nodes, and a list of edges between
them. We require an API to extract source and destination nodes from an edge
(`srcOf` and `dstOf` respectively), as well as well-formedness conditions on
both. We additionally distinguish a special `entry` node to start the analysis
from.
```lean
class AnalysisCFG (Node Edge : Type)
    [DecidableEq Node] [DecidableEq Edge] where
  nodes : List Node
  edges : List Edge
  entry : Node
  srcOf : Edge -> Node
  dstOf : Edge -> Node
  entry_mem : entry ∈ nodes
  srcOf_mem :
    ∀ e ∈ edges, srcOf e ∈ nodes
  dstOf_mem :
    ∀ e ∈ edges, dstOf e ∈ nodes
```

The well-formedness conditions could instead be enforced with the use of a
dependent type `NodeOf g` carrying its membership proof, but that proved to be
more burdensome for the user, and the more explicit formulation was maintained.
The `Node` and `Edge` types are deliberately abstract to allow full flexibility
in the end user's choice of model.

== Finite height bounded semilattices

The properties of finite-height, bounded semilattices lie at the core of
monotone frameworks, and most of the properties we provide, like termination and
soundness, follow directly from them. Analyses in our framework are stated over
join-semilattices (isomorphic to their meet counterpart), so we describe them in
detail.

We say that a type is of #emph[finite height] with the following typeclass:

```lean
class FiniteHeight (L : Type) [Max L] where
  remainingHeight : L -> Nat
  height_join : ∀ a b, a ⊔ b ≠ a -> remainingHeight (a ⊔ b) < remainingHeight a
```

We require every chain in $L$ to have a decreasing bounded measure, meaning that
any join between two elements strictly decreases the measure of its operands, if
it is not equal to them. The finite-heightness requirement on lattices is
required to guarantee termination. While all of the analyses we consider are
defined over lattices of finite height, other techniques to establish
termination exist, such as widening; we will not consider them here as these are
not used in Kotlin.

With this definition, we can define semilattices. Consider a join operation
$dot lub dot : L times L -> L$ over elements of type $L$. This operation induces
an ordering. For all $a, b in L$, $a squb b space eq.triple space a lub b = b$.

We say that a lattice is #emph[bounded] if there exists a distinguished element
$bot : L$ such that $forall a in L, bot squb a$.

With these definitions in hand, modelling the #strong("F")inite #strong(
  "H",
)eight #strong("B")ounded #strong("S")emi#strong("lattice") is relatively
straightforward:

```lean
class FHBSLattice (L : Type) [Max L] [Bot L] [FiniteHeight L] where
  join_comm : ∀ a b : L, a ⊔ b = b ⊔ a
  join_assoc : ∀ a b c : L, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  join_idem : ∀ a : L, a ⊔ a = a
  bot_le : ∀ a : L, ⊥ ⊑ a
```

#let lam(x) = $lambda #x. space$

==== Generic #fhbsls.
There are a few very common shapes of lattices that appear when designing
analyses. We provide templates for those and prove that they too are #fhbsl:

- *The product lattice* -- given two #fhbsls $L_1$ and $L_2$, $L_1 times L_2$ is
  a #fhbsl with $(a_1, a_2) lub (b_1, b_2) = (a_1 lub_1 b_1, a_2 lub_2 b_2)$.
- *The boolean lattice* -- ${bot, top}$ is a lattice with
  $a lub b = cases(bot & "if" a = b = bot, top & "otherwise")$.
- *The domain lattice* -- given a #fhbsl $L_1$ and $n in NN$, the map
  $"Fin" n -> L_1$ is a #fhbsl with $m_1 lub m_2 = lam(i) m_1(i) lub_1 m_2(i)$.
  Here, $"Fin" n$ represents a finite type of size exactly $n$.
- *The powerset lattice* -- given an $n in NN$, the powerset lattice is
  represented using the domain lattice with $n$ and the boolean lattice. This
  encodes the lattice of characteristic functions of a set. One can see that
  this induces the join to be set union and the order to be the subset relation.

We end up making extensive use of the domain lattice during our formalization,
as the basis of the representation of a finite number of variables in a program.

== Language semantics and dataflow analysis

Our framework is only as useful as it allows us to relate abstract structures to
real-world constructs. We do so by allowing the user to define their language
semantics on the CFG they provide:

```lean
class LangSem (Edge Node State : Type) where
  LStep : Edge -> State -> State -> Prop
  LStutter : Node -> State -> State -> Prop
  IsInit : State -> Prop
```

The framework requires a stepping relation on the edges of the CFG, to relate
input and output states. Since the abstract and concrete semantics might not
always be completely synchronized, we allow the user to provide an `LStutter`
condition for a given node, to allow the concrete semantics to take a step that
has no corresponding CFG transition. Finally, we ask of the user to define a
predicate characterizing all possible initial states. On these semantics we
define a reachability condition over states, as the reflexive transitive closure
of `LangSem.LStep` and `LangSem.LStutter` starting from any state such that
`LStutter.IsInit`.

The desired properties of `LangSem` are expressed in terms of a dataflow
analysis (DFA). To specify an analysis it is enough to provide the transfer
functions and the starting lattice value.

```lean
structure DFA (Node Edge : Type) where
  L : Type
  nodeTransfer : Node -> L -> L
  edgeTransfer : Edge -> L -> L
  entry        : L
```

With this, we are ready to state the required properties of the dataflow
analysis with regards to some language semantics.

#[
  #set text(9pt)

  ```lean
  structure DFASemantics (A : DFA Node Edge) where
    Coh : A.L -> State -> Prop
    preserve_entry :
      ∀ {σ : State}, LangSem.IsInit σ -> Coh A.entry σ
    preserve_step :
      ∀ {e : Edge} {σ σ' : State} {ℓ : A.L},
        LangSem.LStep e σ σ' -> Coh ℓ σ -> Coh (A.transferAlong g e ℓ) σ'
    preserve_stutter :
      ∀ {n : Node} {σ σ' : State} {ℓ : A.L},
        LangSem.LStutter g n σ σ' -> Coh ℓ σ -> Coh ℓ σ'
  ```
]

This is where the user finally defines their #coh relation, and where they are
required to show that:

+ #coh relates the abstract entry value to any initial concrete state;
+ #coh is preserved when a related abstract transfer application and concrete
  step along the CFG take place;
+ #coh is preserved when the concrete semantics take a step on a node on which
  the semantics stutter.

These simple definitions are enough for users to define complex analyses, and
establish non-trivial correctness relations for them. These obligations seem
heavy, but they allow the framework to run the analysis algorithm and obtain
guarantees on the result. Let us discuss what those guarantees are, and how they
are established. w
== Kildall's worklist algorithm

To drive our analyses, we implement and verify the worklist algorithm on #fhbsls
as described in @Kildall73. Provided a CFG $g = (N, E)$ and a DFA with transfer
functions $f_n, f_e$, the algorithm runs to refine $rho : N -> L$ into its
post-fixpoint:

$
  forall n in N,
  forall s in #succ($G$, $n$), quad f_n (rho(n)) squb rho(s)
$

The algorithm works by maintaining a worklist $l$ of nodes to process. We
initialize $rho$ to $rho_0$, mapping every node into $bot$, and $l$ to $N$

Let $(rho, l) ~> (rho', l')$ denote a single "step" (an iteration) of the
algorithm. When processing a node $n in l$, $rho'$ is computed by joining the
results of the $f_((n', n))$ on all of its incoming edges, before applying the
corresponding $f_n$ and joining it with the current state $rho(n)$.
Mathematically, this yields:

$
  rho'(n) = rho(n) lub f_n (union.sq.big_(n' in "pred"_G (n)) f_((n', n)) (rho(n')))
$

If $rho'(n)$ is different from $rho(n)$, we append the successors of $n$ to the
worklist, since they were affected by the change. This process continues until
the worklist is empty. This procedure might be simple, but it is enough to
compute a post-fixpoint solution, and to guarantee termination on finite height
domains. We sketch the proofs of those properties here:

#theorem[The worklist algorithm terminates.]
#proof[
  We argue that the measure $(h, l) in NN times NN$ decreases with every
  iteration, where $h$ is the sum of the remaining height of $rho(n)$ for every
  $n in N$, and $l$ is the length of the worklist. Let $rho(n), rho'(n)$ be the
  abstract values at $n$ before and after an iteration. Since $a squb a lub b$,
  we know that $rho(n) squb rho'(n)$. We therefore have two cases: if
  $rho(n) = rho'(n)$ there was no change, so $l$ decreases. Otherwise, a better
  result was found, so $h$ decreases.
]

This argument only holds because of the finite height of our lattice, which
gives us a lower bound we can decrease towards. To show that the result of this
algorithm is a post-fixpoint, we borrow a technique from @LaSpina25 to establish
invariants over the algorithm's runtime.

We say that a property $P$ over an intermediate analysis result $rho$ and a
worklist $l$ is #emph[inductive] if $P(rho_0, l_0)$ and
$P(rho, l) -> ((rho, l) ~> (rho', l')) -> P(rho', l')$
where $~>$ denotes a single iteration of the algorithm as before. We denote the
final result of the algorithm with $overline(rho)$. Then, we can show the
following intermediate result:

#lemma[Let $P$ be an inductive property. Then,
  $P(overline(rho), [thin])$.] <thm:iteration-inv>
#proof[By induction on the iterations of the algorithm.]

Using this result, the proof of soundness is relatively straightforward.

#theorem[For any $n in N$, and any transfer function $f_n$, the result of the
  worklist algorithm $overline(rho)$ is a post-fixpoint.] <thm:soundness>
#proof[
  It is easy to check that $P(rho, l) =$
  "$rho "is a post-fixpoint for all" n in.not l$" is inductive. We apply
  @thm:iteration-inv with $P$, concluding the proof.
]

Interestingly, this soundness result does not require the transfer functions in
the analysis to be monotonic. Monotonic transfer functions allow us to show that
$overline(rho)$ is a #emph[least] post-fixpoint, a result that is mechanized in
our framework but that goes unused in our case studies.

Using @thm:soundness, we can finally prove @thm:framework, our main theorem:
#proof(standalone: true)[By induction on steps, using `DFASemantics`'
  initialization and preservation properties, together with the soundness of the
  Kildall algorithm from @thm:soundness]

With the guarantees established, we move onto discussing our application of the
framework, showing its full power in action.

= Application
<sec:appl>

#let null = "null"
#let isnull = "isnull"
#let dec = "let"
#let skip = "skip"
#let Int = "Int"
#let var = "var"
#let Var = "Var"
#let Val = "Val"

#let iif(c, t, f) = $"if" (#c) med {#t} "else" {#f}$
#let wwhile(c, b) = $"while" (#c) med {#b}$

We implement our analyses on Duke, an untyped imperative language designed to be
a simple subset of Kotlin. It contains the required language constructs for the
nullability analysis.

Values #Val are represented by potentially nullable integers. Values which are
either #null or the integer 0 are considered falsy. Strictly positive integers
are considered truthy. We can further compose values into expressions with
variables and simple operators. Statements consist of variable declarations,
assignments, if- and while-statements; its entire syntax is defined in
@fig:duke-syn. By allowing values to be nullable we model Kotlin's approach to
flow typing, including the use of _consequents_ which we will present shortly.


#figure(
  caption: [Syntax of Duke],
)[
  #block(width: 100%)[$
    xor & ::= + | - | * | < | = | and \
      e & ::= null | Int n | Var x | isnull e | !e | e xor e \
      s & ::= var x := e | x = e | iif(e, s, s) \
        & quad | wwhile(e, s) | skip | s; s
  $]
]<fig:duke-syn>

To define the concrete semantics of Duke, we must first present its CFG
construction.

#let NodeID = $sans("NodeID")$
#let NodeKind = $sans("NodeKind")$

We represent nodes with simple identifiers #NodeID, where edges are pairs of
such #[#NodeID]s. We use #NodeKind to differentiate kinds of nodes in the CFG,
corresponding to program constructs:

$
  NodeKind := x = e | "assume" e | skip
$

The assignment node simply binds the value of the expression $e$ to the variable
named $x$. It serves both declarations and mutations. The synthetic assume node
is inserted after conditionals to indicate which branch was taken. The abstract
interpreter is expected to assume that $e$ holds when traversing an assume node.
This information could be instead stored in edges, but having it in the nodes
leads to a more convenient formalization. Finally, skip, is a node with no
action attached to it.

#figure(
  caption: [
    Statement to CFG translation for Duke. Dotted nodes represent subgraphs.],
)[
  #grid(columns: (1fr, 1fr, 1fr, 1fr), gutter: 1em, align: center + horizon)[
    #image("assets/decl.svg", width: 40%)
  ][
    #image("assets/if.svg", width: 90%)
  ][
    #image("assets/while.svg")
  ][
    #image("assets/seq.svg", width: 60%)
  ][ $dec x = e, x = e$ ][ $iif(c, t, f)$ ][ $wwhile(c, b)$ ][ $s_1; s_2$ ]
]<fig:duke-cfg>


In @fig:duke-cfg we show the translation of Duke's statements into its CFG. A
conditional over an expression $c$ always create two edges from a #skip node
into nodes for $"assume" c$ and $"assume" !c$.

#let redu = $arrow.b.double$
#let cat(i) = $corner.l.t #i corner.r.t$
#let forest(..stuff) = align(center)[#block(inset: 1em)[
  #rule-set(column-gutter: 3em, row-gutter: 1.5em, ..stuff)
]]

To define the concrete semantics on CFGs we first present the big-step reduction
for expressions into values in @fig:expr-eval. We represent the environment map
with $sigma : Var harpoon Val$. We denote by $cat(xor)$ the interpretation of
the binary operator $xor$. Notice that we can have stuck terms in three cases:

+ if either operand of $xor$ is #null, or
+ if the operand of $isnull$ is #null, or
+ if for $Var x$, $x$ is not defined in $mu$.

With that we define the concrete semantics of statements directly on the CFG as
seen in @fig:cfg-sem. The semantics are expressed as reductions on
$(n, sigma) in N times (Var harpoon Val)$. They are designed to integrate pretty
naturally with the existing features of the `Chartreux` framework, all while
remaining the fundamental ground-truth semantics for this language.

We again encounter reductions which can get stuck, either because an expression
reduction failed or because an assume node contains a falsy expression. It will
be precisely the role of the dataflow analysis to show that properly formed
programs cannot get stuck during execution.

When integrating all of the above with `Chartreux`, we can think about what
steps are "loud" and which are "stutter": since CFG reductions are the ground
truth `LStep` semantics, we do not have to define anything as stutter as there
is no correspondence to be drawn. The concrete state `State` simply becomes
$Var harpoon Val$.

#figure(caption: [Big-step semantics for Duke expressions])[
  #let exprs = (
    prooftree(rule(
      name: [null],
      $sigma tack null redu null$,
    )),
    prooftree(rule(
      name: [int],
      $sigma tack Int n redu Int n$,
    )),
    prooftree(rule(
      name: [var],
      $sigma(x) = v$,
      $sigma tack Var x redu v$,
    )),
    prooftree(rule(
      name: [isnullT],
      $sigma tack e redu null$,
      $sigma tack isnull e redu Int 1$,
    )),
    prooftree(rule(
      name: [isnullF],
      $sigma tack e redu v$,
      $v != null$,
      $sigma tack isnull e redu Int 0$,
    )),
    prooftree(rule(
      name: [notT],
      $sigma tack e redu Int n$,
      $n != 0$,
      $sigma tack !e redu Int 0$,
    )),
    prooftree(rule(
      name: [notF],
      $sigma tack e redu Int 0$,
      $sigma tack !e redu Int 1$,
    )),
    prooftree(rule(
      name: [binop],
      $sigma tack e_1 redu Int n_1$,
      $sigma tack e_2 redu Int n_2$,
      $v = n_1 med cat(xor) med n_2$,
      $sigma tack e_1 xor e_2 redu v$,
    )),
  )

  #forest(..exprs)
]<fig:expr-eval>



#figure(caption: [Duke CFG Semantics. $"kind" : NodeID -> NodeKind$ identifies
  node IDs with their kinds.])[
  #let trees = (
    prooftree(rule(
      name: [skip],
      $"kind"(n) = skip$,
      $n' in "succ"(n)$,
      $(n, sigma) -> (n', sigma)$,
    )),
    prooftree(rule(
      name: [assign],
      $"kind"(n) = (x = e)$,
      $sigma tack.r e arrow.b.double v$,
      $n' in "succ"(n)$,
      $(n, sigma) -> (n', sigma[x mapsto v])$,
    )),
    prooftree(rule(
      name: [assume],
      $"kind"(n) = "assume" e$,
      $sigma tack.r e arrow.b.double Int m$,
      $m != 0$,
      $n' in "succ"(n)$,
      $(n, sigma) -> (n', sigma)$,
    )),
  )
  #forest(..trees)
]<fig:cfg-sem>





== Nullability with consequents

The point of nullability analysis is to statically determine problematic usages
variables which have the value #null. We now present the entire nullability
analysis with boolean witnesses which implies the absence of stuck terms.

#let AbsVal = math.sans("AbsVal")
#let AbsFact = math.sans("AbsFact")
#let AbsConseq = math.sans("AbsConseq")
#let FHL = [finite height lattice]
#let fst = "fst"
#let snd = "snd"
#let nonnull = "nonnull"

We first need a few lattices. First, $AbsVal$:

#block(width: 100%, inset: 1em)[#align(center)[#diagram({
  let ltop = (0, 0)
  let lbot = (0, 1)
  node(ltop, $top$)
  node(lbot, $nonnull$)
  edge(ltop, lbot)
})]]

Which will abstract whether some variable is definitely not null ($nonnull$) or
we don't know enough about it ($top$). This is of finite height since it has a
finite amount of elements. The join is defined as follows:

$
  nonnull lub a = a lub nonnull & := a \
                    top lub top & := top
$

The bottom element of $AbsVal$ is $nonnull$. The join (and the induced order)
fulfills the requirements of being a #FHL.

Next, we use the domain lattice template to create
$AbsConseq : Var^n -> AbsVal$. Since $AbsVal$ is a #FHL then so is $AbsConseq$.
It stores the consequent of the implication that if a variable is truthy, then
the assertions in $AbsConseq$ hold. For example, in the program
$x = !(isnull y) and !(isnull z)$ not only do we know that $x$ is $nonnull$, but
also that it is a witness of $y$ and $z$ being $nonnull$. If $x$ evaluates to a
truthy value, we will know both $y$ and $z$ is not null. This makes our domain
relational.

Finally, since we want to store nullability information for each variable
separately, we wrap $AbsVal$ and $AbsConseq$ in a domain over all variables,
$AbsFact : Var^n -> AbsVal times AbsConseq$. Since both $AbsVal$ and $AbsConseq$
are #(FHL)s, so is $AbsVal times AbsConseq$. Similarly, so is the entire
$AbsFact$.

To define the CFG transfer functions, we first need to define abstract
evaluation of expressions:

$
  "aeval" : AbsFact times "Expr" & -> AbsVal \
              "aeval"(rho, null) & := top \
             "aeval"(rho, Int n) & := nonnull \
             "aeval"(rho, Var x) & := fst(rho(x)) \
          "aeval"(rho, isnull e) & := nonnull \
                "aeval"(rho, !e) & := nonnull \
       "aeval"(rho, e_1 xor e_2) & := "aeval"(rho, e_1) lub "aeval"(rho, e_2)
$

We additionally need a way to extract consequent information from an expression.
We want to answer the question "given an expression $e$, what nullability
information do we gain when assuming $e$ is truthy?".

$
  "exprConseq" : AbsFact times "Expr" & -> AbsConseq \
  "exprConseq"(rho, Var x) & := lambda y. cases(nonnull &quad snd(rho(x))(y) = nonnull, top &quad "otherwise") \
  "exprConseq"(rho, !isnull (Var x)) & := lambda y. cases(nonnull &quad x = y, top &quad "otherwise") \
  "exprConseq"(rho, e_1 and e_2) & := lambda y. cases(nonnull &quad "exprConseq"(rho, e_1)(y) = nonnull or "exprConseq"(rho, e_2)(y) = nonnull, top &quad "otherwise") \
  "exprConseq"(rho, e) & := lambda\_. top \
$

When looking at a variable we consult the consequents that variable holds. If we
assume $!isnull (Var x)$ holds, it of course means that $x$ is not null. In case
of a conjunction we consider both sides holding true. Finally, for all other
cases there is nothing we can say.

This allows us to define the node transfer function:
$
  f : NodeKind -> AbsFact & -> AbsFact \
  f(x = e)(rho) & := lambda y. cases(("aeval"(rho, e), "exprConseq"(rho, e)) &quad x = y, (fst(rho(y)), lambda\_. top) &quad "otherwise") \
  f("assume" e)(rho) & := lambda y. cases((nonnull, snd(rho(y))) &quad "exprConseq"(rho, e)(y) = nonnull, rho(y) &quad "otherwise") \
  f(skip)(rho) & := rho
$

Where $fst$ and $snd$ are standard projection functions to the first and second
element respectively. In the case of assignment $x = e$, we assign the #AbsVal
to $x$ from the abstract evaluation of $e$ and we extract the consequents coming
from $e$. For all other variables in the program we keep their #AbsVal but
invalidate all consequents since they might have been invalidated due to the
mutation of $x$. The transition for $"assume" e$ extracts the consequents from
$e$ and immediately assumes them to hold.

=== Correctness.
For an abstract state $rho : AbsFact$ and a concrete state $sigma : "State"$, we
define the following coherence relation:

$
  coh(rho, sigma) =& forall x in "dom"(rho).\
  &[fst(rho (x)) = nonnull -> sigma (x) != null] and\
  &[forall y in "dom"(rho). med snd(rho (x)) (y) = nonnull and sigma (x) = Int n and n != 0 -> sigma (y) != null]
$

The first half of the coherence is the correctness property of the analysis. The
second half of the correspondence gives a denotation for the consequents, needed
for proving step preservation. Then, once the framework obligations are
fulfilled, we combine the nullability analysis with a standard initialization
analysis, leading to the proof of the safety theorem of Duke:

#theorem[
  Let $g$ be a program such that successful initialization and nullability
  analyses have been carried out. Let $(n, sigma)$ be a reachable execution
  configuration when running $g$. Then, either:
  - $n$ is the exit node of $g$;
  - $n$ is an $"assume"$ node whose condition is false;
  - there exists a node $n'$ and a state $sigma'$ such that
    $(n, sigma) -> (n', sigma')$.
]

At exit nodes we naturally cannot take a step, and since an $"assume" c$ node is
always paired with $"assume" !c$, one of them must be necessarily false.

== Function contract checking

#let ca = "call"
#let call(f, s) = $"call" #f thin { #s }$
#let invoke = "invoke"
#let Gk = $G_kappa$

The second problem concerns the CFG rewrites induced by calls-in-place
contracts. At a call site, the compiler analyzes the body of a lambda as though
it occurred directly in the caller. The edges around this copy encode whether
the lambda may be skipped or repeated. This makes information produced inside
the lambda available to the caller's dataflow analysis, but introduces a proof
obligation: executions that enter another function and invoke a closure must be
represented by paths through the local rewritten graph.

We study this problem in _FDuke_, an extension of Duke with function calls and
lambda invocation. Its statements have two additional forms:

#block(width: 100%, inset: 1em)[$
  s & ::= ... | #call($f$, $s$) | invoke
$]

The statement #call($f$, $s$) passes $s$ as the closure argument of $f$, while
#invoke executes the current function's closure argument. Lambdas have no
parameters of their own, but execute in the store captured at the call site. A
program consists of a main statement and a finite function environment
$Phi : "Id" harpoon (kappa times "Stmt")$. The invocation kind
$kappa in {epsilon, 1, +, ?}$ denotes, respectively, an unknown number of
invocations, exactly one, at least one, or at most one.

#figure(
  caption: [Contract-dependent CFG fragments in FDuke. The lambda body ${s}$ is
    copied into the caller for analysis; the dotted arrow depicts the CEK
    machine's call/return control transfer and is not an edge of the analysis
    graph.],
)[
  #grid(columns: (1fr, 1fr, 1fr, 1fr), gutter: 1em, align: center + horizon)[
    #image("assets/unknown.svg")
  ][
    #image("assets/exactly_once.svg")
  ][
    #image("assets/at_most_once.svg")
  ][
    #image("assets/at_least_once.svg")
  ][ $epsilon$ ][ 1 ][ ? ][ `+` ]
]<fig:fduke-cfg>

#let langle = $chevron.l$
#let rangle = $chevron.r$

For a call node with lambda entry $"en"_L$, lambda exit $"ex"_L$, and return
node $r$, the lowering emits the fragments in @fig:fduke-cfg. Every fragment has
edges from the call to $"en"_L$ and from $"ex"_L$ to $r$. The kind $?$ adds a
bypass edge from the call to $r$, while $+$ adds a back-edge from $"ex"_L$ to
$"en"_L$. The unknown kind $epsilon$ contains both edges, and the kind $1$
contains neither. The resulting paths execute the inlined body any number of
times admitted by the contract:

$
  "admits"(epsilon, k) & := top \
        "admits"(1, k) & := (k = 1) \
        "admits"(+, k) & := (1 <= k) \
        "admits"(?, k) & := (k <= 1).
$

Lowering also records construction-time metadata for the call site: its call
node, callee, lambda identifier, invocation kind, inline entry and exit, return
node, and source lambda body. The dotted arrow in @fig:fduke-cfg represents how
the concrete CEK machine uses this metadata to enter the callee and eventually
return to $r$; it is not an additional CFG edge. The generated family certifies
that every structural edge of the corresponding contract fragment is present.
These certificates can be erased after construction while preserving graph and
call-site lookup exactly.

=== Concrete semantics.
Lowering an FDuke program produces a family of CFGs: one graph for `main`, one
for each function body, and one for every lambda literal. The concrete semantics
is a CEK machine over this family. Its configurations have the form
$langle n, sigma, rho, K rangle$, where $n$ identifies both a graph and a node,
$sigma$ is the current store, $rho$ is an optional closure, and $K$ is a stack
of continuations. A closure records a lambda's entry and exit nodes, its
captured closure, and its captured store.

#figure(caption: [Function and invocation semantics], placement: top)[
  #let trees = (
    prooftree(rule(
      name: [call],
      $"kind"(n) = #call($f$, $ell$)$,
      $r in "succ"_"summary" (n)$,
      $langle n, sigma, rho, K rangle ->
      langle "en"_f, ·, "some"(C), call(r, rho) :: K rangle$,
    )),
    prooftree(rule(
      name: [invoke],
      $"kind"(n) = invoke$,
      $rho = "some"(langle "en"_L, "ex"_L, rho_d, sigma_d rangle)$,
      $r in "succ"(n)$,
      $langle n, sigma, rho, K rangle ->
      langle "en"_L, sigma_d, rho_d, "inv"(r, rho, sigma) :: K rangle$,
    )),
    prooftree(rule(
      name: [return-call],
      $"succ"(n) = emptyset$,
      $langle n, sigma, "some"(langle "en"_L, "ex"_L, rho_c, sigma_c rangle), call(r, rho') :: K rangle ->
      langle r, sigma_c, rho_c, K rangle$,
    )),
    prooftree(rule(
      name: [return-invoke],
      $"succ"(n) = emptyset$,
      $langle n, sigma, rho', "inv"(r, "some"(langle "en"_L, "ex"_L, rho_d, sigma_d rangle), sigma_f) :: K rangle ->
      langle r, sigma_f, "some"(langle "en"_L, "ex"_L, rho', sigma rangle), K rangle$,
    )),
  )
  #forest(..trees)
]<fig:function-semantics>

The relevant rules are shown in @fig:function-semantics. Calling $f$ saves the
lambda and the caller's store in a closure, starts the function body with an
empty store, and pushes the return point. An #invoke starts the saved lambda in
its captured store and pushes the function's current store. Returning from the
lambda updates the closure with the lambda's resulting store and resumes the
function; returning from the function restores this store in the caller. These
rules give calls their ground-truth behavior independently of the CFG rewrite.

=== Checking contracts.
#let Cnt = math.sans("Cnt")
Before relying on a contract, we verify it with a counting analysis. Its domain
is $Cnt = cal(P)({0, 1, omega})$, where $omega$ represents two or more
invocations. It is a finite-height powerset lattice ordered by inclusion, with
union as join and the empty set as $bot$. The entry value is ${0}$. At an
#invoke node, every possible count is incremented according to $0 + 1 = 1$,
$1 + 1 = omega$, and $omega + 1 = omega$; all other transfer functions are the
identity.

The concrete semantics used for this analysis pairs the store with a ghost
natural-number counter. Its coherence relation states that the abstraction of
the concrete counter belongs to the current element of #Cnt. Incrementing the
counter and applying the transfer function preserve coherence, so @thm:framework
establishes that every concrete invocation count reaching a node is included in
the computed result.

Let $overline(rho)_f$ be a post-fixpoint obtained for the body of $f$, and let
$n_f$ be its exit node. The declared contract is accepted when:

$
  1 & <-> overline(rho)_f (n_f) = {1} \
  + & <-> 0 in.not overline(rho)_f (n_f) \
  ? & <-> omega in.not overline(rho)_f (n_f).
$

No restriction is imposed for $epsilon$. We write $sans("FamilyChecked")(p)$
when every function CFG in $p$'s generated family has such a post-fixpoint
satisfying its declared contract. Checkedness is required for the whole family,
since a function may call another function whose invocation of its own lambda
affects the first function's count.

=== Correctness of the rewrite.
The proof relates the interprocedural CEK semantics directly to the structural
analysis graph #Gk. A step at an ordinary node has its usual store effect, while
a step leaving a call node is store-preserving. The effect of a complete call is
therefore represented by traversing the copied lambda body zero or more times,
as allowed by its contract fragment.

This direct account depends on certified lowering. For every call, the builder
records a #emph[call gadget] containing the call and return nodes, inline-body
endpoints, lambda identifier, invocation kind, and source body. It proves that
all edges prescribed by that invocation kind are present. A certificate-bearing
family additionally connects the inline copy to the separately generated lambda
component, including the node offset, shifted lambda identifiers, edges, and
nested call gadgets. Erasing the proofs recovers the execution-facing CFG family
and preserves both component and gadget lookup. Consequently the projection
never infers provenance from an arbitrary graph after the fact.

#theorem[
  Let $p$ be an FDuke program such that $sans("FamilyChecked")(p)$. Every CEK
  execution that starts and ends in the same component with an empty
  continuation and starts without a closure is represented by a sequence of
  store steps in that component's structural graph #Gk, with the same initial
  and final stores.
] <thm:fduke-projection>

The Lean theorem `balanced_project` proves a stronger statement by strong
induction on the length of a #emph[balanced] CEK run: throughout the run, the
continuation has a fixed stack as suffix, and the endpoints have exactly that
stack. Its conclusion simultaneously retains:

+ a bounded chain describing every completed invocation of the ambient, evolving
  closure, including each lambda-body CEK run;
+ the exact number $q$ of links in that chain;
+ a run of a ghost-counting semantics from $(sigma, 0)$ to $(sigma', q)$ on #Gk;
  and
+ the required store-only run from $sigma$ to $sigma'$ on #Gk.

The bounds make every recursively projected lambda or callee body strictly
shorter than the enclosing run. Closure and continuation well-formedness keep
all referenced components resolvable, while a fixed pair of lambda endpoints
ensures that an evolving closure still denotes the same body. This strengthening
is what makes nested calls and invocations compositional. Two projected segments
compose by concatenating their closure chains and store runs; the second
ghost-counted run is shifted by the first segment's final count.

Assignment, assumption, and skip steps prepend the corresponding graph edge and
use the induction hypothesis on the tail. A return that would pop below the
fixed continuation suffix is impossible. The two interprocedural cases require
explicit CEK-run decomposition:

+ For #invoke, the run is split at the matching return from the lambda. The
  completed lambda body becomes one link in the ambient closure chain, its
  captured environment and store are updated, and the strictly shorter caller
  tail is projected recursively. The invoke node increments the ghost counter
  once but is a store-identity step in the store-only projection.
+ For #call, the run is split at the matching return from the callee into the
  completed callee body and the caller tail. Projecting the callee records the
  exact number $k$ of times it invoked its callback. Each recorded standalone
  lambda run is recursively projected and shifted into the certified inline copy
  at the caller's call site, including nested gadgets. Counting soundness puts
  the abstraction of $k$ in the callee's exit result; family checkedness
  supplies its verdict, from which $"admits"(kappa, k)$ follows. The certified
  gadget is then replayed: $k = 0$ uses the bypass, $k > 0$ uses the entry and
  exit edges, and all iterations after the first use the back-edge. Finally this
  call path is composed with the recursively projected caller tail.

Specializing the strengthened theorem to an empty continuation and no initial
closure yields @thm:fduke-projection (the Lean theorem `cek_projection`). The
last correctness layer is deliberately independent of programs and contracts.
The store-step semantics used by the projection and the semantics expected by an
arbitrary analysis have the same structural graph and loud steps, so
reachability transports edge by edge. Applying the generic post-fixpoint
soundness theorem @thm:framework then gives the public Lean theorem
`kappa_rewrite_correct`.

#theorem[
  Let $p$ be an FDuke program with a checked function family, and let $g$ be one
  of its CFG components. Suppose an analysis $A$ over #Gk has a coherence
  relation preserved by its transfer functions, and let $rho$ be a post-fixpoint
  whose entry contains the analysis entry value. For every state $sigma$ reached
  at node $n$ by a balanced CEK execution of $p$ from the entry of $g$,
  $coh(rho(n), sigma)$ holds.
] <thm:fduke>

The theorem is independent of the particular dataflow domain. In particular, the
initialization and nullability analyses used for Duke also run on the rewritten
FDuke graph, with the same correctness guarantees as in the environment without
function calls.

= Discussion <sec:discuss>

/*
== Related Work

Given their ubiquity and critical applications they have enabled, static
analysis approaches have been verified under many forms.

=== Verified Compiler Construction.
CompCert @CompCert is a verified compiler for a subset of C. The compiler correctness is based on an approach of
bisimulation between optimized and unoptimized code. A similar effort for the Java language has been carried through by the Jinja
@Jinja06 project. Finally, CakeML @cakeml is a fully bootstrapped verified compiler for a subset of standard ML. These approaches differ from ours as they focus on optimizations while we directly target aiding type checking.


=== Verified Static Analysis.
Verasco @Verasco is a project providing dataflow analysis capabilities to CompCert. Later, a more language-agnostic approach using iTrees emerged @iTree providing a solid but complicated foundation for abstract interpretation.
*/

== Future work

This tool is under very active development. The end-to-end function-contract
derivation presented here is mechanized, while `Chartreux` as a framework has
multiple paths for improvement. The integration of a WTO-based solver @LaSpina25
could provide better efficiency and accuracy of computed fixpoints.
Additionally, it would be beneficial if the framework provided primitives for
the handling of function calls, given the current burden on the users. Lastly,
the framework could provide alternative formalization paths like allowing for
non-finite height lattices with a widening operator, or letting the user define
correctness by means of a Galois connection whenever more convenient.

On the other hand, a more complete formalization of Kotlin's analyses requires
extending the verified function contract model with more realistic language
constructs. In a real-world compiler, aliasing, exceptions, and other runtime
dangers are real sources of hidden unsoundness, and our framework can be very
useful in the study of such pitfalls. Additionally, formalizing part of Kotlin,
and showing correspondence between regular small-step semantics and the CFG
execution will increase our confidence that the CFG semantics are fully
representative.

== Conclusion <sec:conc>

We describe the design and implementation of a foundational, language-agnostic,
formally verified framework for exploration, specification, and verification of
dataflow analyses that #emph[properly capture the semantics of the enclosed
  language]. The framework is minimal and low obligation. We apply it to modern
analyses to obtain formal guarantees and increased understanding of the Kotlin
language. We trace a clear path of future work to graduate this project from a
proof of concept to a versatile, extensible and easy-to-use tool, as a companion
to aid the tasks of analysis engineers.

==== Acknowledgements
We deeply thank Kameilya Golova for her mentoring throughout this work and for
providing invaluable feedback on the paper.

==== Artifact availability
The framework together with Duke/FDuke and their analyses are available at
`https://github.com/quartztz/chartreux`.

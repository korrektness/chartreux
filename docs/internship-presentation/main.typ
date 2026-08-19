#import "@preview/slydst:0.1.5": definition, slides, theorem, title-slide
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#let fg = rgb("#191920")
#let bish = rgb(80, 150, 150)
#let blueish = color.hsl(180deg, 50%, 25%)
#let redish = rgb(160, 70, 60)

#let lan = math.chevron.l
#let ran = math.chevron.r

#set text(size: 9pt, hyphenate: true, font: "Public Sans")

#show: slides.with(
  subslide-numbering: "(i)",
  layout: "large",
  ratio: 16 / 10,
  title-color: none,
)

#show raw: set block(fill: silver.lighten(65%), width: 100%, inset: 1em)
#show raw: set text(font: "Fira Code", size: 1em)

// #let theorem = it => [
//   #align(center)[#block(width: 81%, fill: silver.lighten(65%), inset: 1em)[#align(
//     left,
//   )[*Theorem.* #it]]]
// ]

//#let theorem = it => align(center)[#block(inset: 0em, width: 85%)[#align(left)[#theorem[#it]]]]

#let theorem(body, name: none, numbered: true) = [#figure(
  body,
  kind: "aparte",
  supplement: [Theorem],
  caption: name,
  numbering: if numbered { n => counter(heading).display() + [#n] } else {
    none
  },
)]
#let definition(body, name: none, numbered: true) = figure(
  body,
  kind: "aparte",
  supplement: [Definition],
  caption: name,
  numbering: if numbered { n => counter(heading).display() + [#n] } else {
    none
  },
)

#show figure.where(kind: "aparte"): set align(start)
#show figure.where(kind: "aparte"): it => block(
  outset: (left: -8pt),
  inset: (left: 16pt, top: 4pt, bottom: 4pt),
  width: 100%,
  breakable: true,
  stroke: (left: bish),
  spacing: 12pt,
  {
    strong({
      it.supplement
      if it.numbering != none {
        [ ]
        it.counter.display("1")
      }
    })
    [. ]
    if it.caption != none [ (#emph(it.caption.body)) ]
    it.body
  },
)

#let proof(sketch: false, it) = [
  #if sketch {
    [_Proof sketch._]
  } else {
    [_Proof._]
  } #it
]

#let one-col(
  it,
) = [
  #align(horizon)[#block(inset: (y: 1em, x: 3em))[#it]]
]

#let two-col(
  left,
  right,
  columns: (1fr, 20em),
) = [#align(horizon)[#grid(columns: columns, inset: 1em)[#left][#right]]]

#let TODO = it => text(fill: purple)[TODO: #it]

#title-slide[
  #v(1fr)
  #[
    #set text(size: 2em, weight: "bold", fill: blue.darken(40%))
    #set par(leading: 0.5em)
    Formally verified dataflow analyses\ for Kotlin
  ]
  #v(-0.5em)
  *End of Internship Presentation*
  #v(1fr)

  #set text(size: 0.8em)
  _Jacopo Philip Moretti_ [he/they]\
  _Marcin Wojnarowski_ [he/him]#h(1fr) 19.08.2026
]

== Introduction

#two-col[
  Satellite project to the "Uniqueness types for Kotlin" proposal.

  In particular, the bridge between the *theoretical framework* of uniqueness
  types vs the *practical implementation* as a dataflow analysis compiler pass.

  *Internship goal.* Under what conditions is dataflow analysis correct? Does
  Kotlin respect these conditions? What tools can we design to help the language
  team with defining correct analyses?

  #align(center)[#block(width: 80%, fill: blue.lighten(65%), inset: 1em)[
    #align(left)[*Result.* `Chartreux`! A framework to define analyses and show
      their correctness with respect to program semantics!

      And instantiations of it to analyses from the Kotlin compiler.]
  ]]
][
  #align(center)[
    #image(width: 50%, "jacopo.png") Jacopo Philip Moretti #image(
      width: 50%,
      "marcin.png",
    ) Marcin Wojnarowski

    Both prev @ EPFL!
  ]
]

== Formalization framework

#let r = prooftree(rule(
  name: [assign],
  $"kind"(n) = (x = e)$,
  $sigma tack.r e arrow.b.double v$,
  $n' in "succ"(n)$,
  $(n, sigma) -> (n', sigma[x mapsto v])$,
))

#let coh = $sans("Coh")$
#let coh-def = $coh subset.eq L times S$


#one-col[
  `Chartreux` is a *generic* framework for verifying analyses!
  === 1. Language

  #show grid.cell: it => align(center)[#it]
  #set grid.cell(stroke: 0.1pt, inset: 1em)
  #block(inset: 1em)[
    #grid(columns: (12em, 1fr))[
      #image(height: 40%, "assets/graph_example.svg")
    ][
      #set text(size: 8pt)
      $#r$
    ][CFG][Stepping semantics for a CFG]
  ]

  // The usual workflow for the framework is:
  // + Specify the language and CFG shape.
  // + Define special semantics over the CFG, capturing the relevant information
  //   for the analysis.
  // + Specify the analysis and correctness predicate for the analysis $coh$.
]

#pagebreak()

#one-col[
  === 2. Analysis

  #show grid.cell: it => align(center)[#it]
  #set grid.cell(stroke: 0.1pt, inset: 1em)
  #block(inset: 1em)[
    #grid(columns: (10em, 1fr, 18em))[
      #diagram({
        let ltop = (0, 1 / 4)
        let l2 = (-0.4, 6 / 4)
        let c2 = (0, 6 / 4)
        let r2 = (0.4, 6 / 4)
        let l1 = (-0.25, 3 / 4)
        let r1 = (0.25, 3 / 4)
        let bot = (0, 8 / 4)
        node(ltop, ${0, 1, omega}$)
        node(l1, ${0, 1}$)
        node(r1, ${1, omega}$)
        node(l2, ${0}$)
        node(c2, ${1}$)
        node(r2, ${omega}$)
        node(bot, $emptyset$)
        edge(ltop, l1)
        edge(ltop, r1)
        edge(l1, c2)
        edge(l2, l1)
        edge(l2, r1)
        edge(r2, l1)
        edge(r2, r1)
        edge(r1, c2)
        edge(c2, bot)
        edge(l2, bot)
        edge(r2, bot)
      })
    ][
      #image(height: 50%, "assets/conc_vs_abs.svg")
    ][
      $
        tack.r coh(rho_0, sigma_0)
      $
      #v(0.5cm)
      $
        rho limits(~~>)^e rho', sigma limits(~>)^e sigma', coh(rho, sigma) tack.r coh(rho', sigma')
      $
    ][Lattice][Coherence predicate][Coherence correctness]
  ]
]

#pagebreak()

#one-col[
  #theorem(name: [Fundamental theorem of analyses])[
    Given:

    - A CFG $g = lan N, E ran$;
    - Language semantics over $S$;
    - An analysis $A$ with transfer functions over a bounded semilattice $L$;
    - A relation $#coh-def$ that's preserved under semantics steps;

    The result $rho : N -> L$ of running Kildall's algorithm on $g$ with
    analysis $A$ is csuch that for all reachable states $sigma : S$ at node
    $n in N$, $coh(rho(n), sigma)$ holds.
  ]

  #text(11pt)[This means that the result of an analysis is _coherent_ with the
    language's semantics!]

  *Why do this?* Model the analyses performed by the Kotlin compiler, to verify
  the correctness of its most quirky features and increase the understanding.

  *Therefore* our efforts were focused on the two distinctive analyses from the
  Kotlin compiler:
  - _(Lesser) Flow typing_,
  - _Function contracts_.
]

= Outcomes

== Nullability with implications

#two-col[
  ```kotlin
  fun calculateTax(cost: Double?): Double? {
    val valid = cost != null && /*1*/cost > 0.0
    /*2*/
    Telemetry.log("calculateTax_valid", valid)
    if (!valid) return null
    /*3*/
    return cost * 0.23
  }
  ```
][
  1. ```kotlin cost != null```
  2. ```kotlin valid``` $=>$ ```kotlin cost != null```
  3. ```kotlin valid``` $thick and thick$ ```kotlin valid``` $=>$
    ```kotlin cost != null```
]

#let nullability-lattice(valid-v, valid-conseq, cost-v, cost-conseq) = {
  let bend = 15deg
  let conseq(l) = if l.len() == 0 { $emptyset$ } else {
    ${#{ l.map(e => e).join($,$) }}$
  }

  diagram(
    spacing: (0.4cm, 0cm),

    node((0, 1), `valid`),
    node((1, 0), valid-v),
    node((1, 2), conseq(valid-conseq)),

    edge((0, 1), (1, 0), "->", bend: -bend),
    edge((0, 1), (1, 2), "->", bend: bend),

    node((0, 5), `cost`),
    node((1, 4), cost-v),
    node((1, 6), conseq(cost-conseq)),

    edge((0, 5), (1, 4), "->", bend: -bend),
    edge((0, 5), (1, 6), "->", bend: bend),
  )
}

#align(center)[
  #show grid.cell: align.with(center)
  #set grid.cell(stroke: 0.1pt, inset: 1em)
  #let diff = underline

  #grid(
    columns: (auto,) * 3,
    nullability-lattice($top$, (), $top$, ()),
    nullability-lattice(diff(`nonnull`), (`cost`,), $top$, ()),
    nullability-lattice(`nonnull`, (`cost`,), diff(`nonnull`), ()),

    [1], [2], [3],
  )
]

#pagebreak(weak: true)

#one-col[
  $
    coh_"nullability" (rho, sigma) := forall x in "dom"(rho), thick rho(x) = #raw("nonnull") => sigma(x) != #raw("null")
  $

  #theorem(name: [Null-safety])[
    In a graph $g$, at a node $n$ and an execution state $sigma$, if the
    nullability analysis is successful, we know that either:
    - There is a successor state $(n', sigma')$ to step to;
    - We are at an `assume c` node s.t. $sigma tack.r$ `!c`;
    - We are at the end of the program.
  ]
  //   #proof(sketch: true)[
  //     Using our main theorem, we know that the nullability analysis gives us
  //     the correct information at $n$. This means that at any operation, we
  //     are guaranteed not to dereference any `null` variable, thereby
  //     preventing the execution from getting stuck.

  //     We proceed by case analysis on the current node kind, applying our
  //     analysis results.
  //  ]
]



== Function contracts

#two-col[
  The Kotlin compiler has unique behavior re: function contracts:
  ```kt
  fun run(lam: () -> Unit) {
    contract {
      callsInplace(lam, InvocationKind.EXACTLY_ONCE)
    }
    lam()
  }

  fun main() {
    val x: Int?

    run { x = 42; }

    println(x + 1) // Inferred to not be null!
  }
  ```
  This result is achieved via special CFG rewrite rules that _assume_ that the
  functions respect their contracts. Is this correct?
][
  #block(height: 100%, width: 100%)[#align(
    horizon + center,
  )[
    #figure(caption: [
      Simplified CFG for #text(font: "Fira Code", size: 1.1em)[main]. In red,
      the inlined parameter graph.
    ])[
      #block(inset: 2em)[#image("assets/graph.svg")]
    ]
  ]]
]

#pagebreak()

#one-col[
  We model a language with function calls and lambda parameters.

  #two-col[
    ```
    run @ 1 :
      invoke;

    p :
      x = null;
      call run {x = 42};
      y = x + 1;
    ```
  ][
    $
      Phi & : "Id" -> "Stmt" times (epsilon, 1, +, ?) \
      Phi & = ["run" |-> lan "invoke", 1ran] \
          & "analyze" lan Phi, p ran
    $
  ]
]

#pagebreak()

=== Counting analysis

#two-col[
  #definition(name: [Counting analysis], numbered: false)[
    - *Lattice:* $L = cal(P)({0, 1, omega})$.

    - *Transfer:* $f_n : "Node" -> L -> L$ s.t.:
      $
        f_n ("invoke")(sigma) & = {e + 1 | e in sigma} \
              f_n (\_)(sigma) & = sigma
      $
      where $0 + 1 = 1$ and $1 + 1 = omega + 1 = omega = omega + 1$.

    - *Join:* $lambda s_1, s_2. s_1 union s_2$.
    - *Coherence:*
    $
      coh_"Counting" (rho, lan k, sigma ran) := "abs"(k) in rho
      quad "where" quad
      "abs"(k) := cases(
        0\, quad & k = 0,
        1\, quad & k = 1,
        omega\, quad & k >= 2
      )
    $
  ]

  Correctness follows from application of the _Fundamental Theorem_.
][
  #align(center)[
    #figure(caption: [Counting analysis lattice])[#diagram({
        let ltop = (0, 1 / 4)
        let l2 = (-0.45, 6 / 4)
        let c2 = (0, 6 / 4)
        let r2 = (0.45, 6 / 4)
        let l1 = (-0.45, 3 / 4)
        let c1 = (0, 3 / 4)
        let r1 = (0.45, 3 / 4)
        let bot = (0, 8 / 4)
        node(ltop, ${0, 1, omega}$)
        node(l1, ${0, 1}$)
        node(c1, ${0, omega}$)
        node(r1, ${1, omega}$)
        node(l2, ${0}$)
        node(c2, ${1}$)
        node(r2, ${omega}$)
        node(bot, $emptyset$)
        edge(ltop, l1)
        edge(ltop, c1)
        edge(ltop, r1)
        edge(l1, c2)
        edge(l2, l1)
        edge(l2, c1)
        edge(l2, r1)
        edge(r2, l1)
        edge(r2, c1)
        edge(r2, r1)
        edge(r1, c2)
        edge(c1, c2)
        edge(c2, bot)
        edge(l2, bot)
        edge(r2, bot)
      })
      #v(1em)
    ]]
]

#pagebreak()

=== Rewrite correctness

#one-col[
  #theorem(name: [FTA with functions])[
    For a _checked_ function family $Phi$, and any program $lan p, Phi ran$, any
    analysis $A$ on the contract-aware CFG of $p$ satisfies the properties of
    the _Fundamental Theorem_.
  ]

  #proof(sketch: true)[
    // The analyses are not interprocedural!
    // Since the lambda
    // parameter only has access to the caller's execution environment, the
    // jump is useless from the point of view of the caller.
    // This means we can define two semantics, with and without jumps,
    // and relate the two:
    #v(1em)
    #figure(caption: [Proof diagram for rewrite correctness])[
      #image(width: 90%, "assets/func_proof_diagram_hor.svg")
      #v(0.5em)
    ]

    // The jump semantics simulate the regular ones through nondeterministic shenanigans.
  ]
]

= Results

== Results
#one-col[
  During our internship, we developed `Chartreux`, and tried to show its
  maturity for large-scale Kotlin formalization efforts. We claim we got close!

  + A framework for specifying and reasoning about analyses;

    _Novel presentation of these algorithms and proofs in Lean! In the process
    of being merged to #link("https://cslib.io")[CSLib]._

  + An application of this framework to a subset of Kotlin;

    _Formal behavior guarantees of Kotlin-specific dataflow analyses (function
    contracts, flow typing)._

  + A conference-submitted paper;

    _Currently under review of the VSTTE workshop committee. Results on Aug 22nd
    (soon!)._

  Code is available on #link("github.com/korrektness/chartreux")[`github`], as
  well as the paper.
]

== Exceptional flow

#one-col[
  - Tried to find unsoundness under our formalization, unsuccessful
  - Difficult to formalize: no edges for transitions
]

#import "@preview/slydst:0.1.5": definition, slides, theorem, title-slide
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#let fg = rgb("#191920")
#let bish = rgb(80, 150, 150)
#let blueish = color.hsl(180deg, 50%, 25%)
#let redish = rgb(160, 70, 60)

#let lan = math.chevron.l
#let ran = math.chevron.r

#set text(size: 12pt, hyphenate: false, font: "Public Sans")

#show: slides.with(
  subslide-numbering: "(i)",
  layout: "large",
  ratio: 16 / 10,
  title-color: none,
)

#set list(indent: 1em)

#show raw: set block(fill: silver.lighten(65%), width: 100%, inset: 1em)
#show raw: set text(font: "Fira Code")
#show raw.where(block: false): set text(size: 1.2em)
#show raw.where(block: true): set text(size: 1.0em)

#show figure.caption: set text(size: 0.7em)

#set figure(numbering: none)

// #let theorem = it => [
//   #align(center)[#block(width: 81%, fill: silver.lighten(65%), inset: 1em)[#align(
//     left,
//   )[*Theorem.* #it]]]
// ]

// #let theorem = it => align(center)[#block(inset: 0em, width: 85%)[#align(left)[#theorem[#it]]]]

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
  #align(horizon)[#block(inset: (y: 0.25em, x: 1em))[#it]]
]

#let two-col(
  left,
  right,
  columns: (1fr, 16em),
) = [#align(horizon)[#grid(columns: columns, inset: 1em)[#left][#right]]]


#let pronouns-allowed = false
#let pronouns = it => if pronouns-allowed [#it] else []

#title-slide[
  #v(50%)
  #[
    #set text(size: 1.25em, weight: "bold", fill: blue.darken(40%))
    #set par(leading: 0.6em)
    Chartreux: Towards Verified Dataflow\ Analyses for Kotlin
  ]

  #v(1fr)

  #align(center)[#pad(y: 1em, x: 3em)[
    #grid(columns: (1fr, 1fr))[
      #image("assets/lean.png", height: 3em)][
      #image("assets/jetbrains.png", height: 2.5em)
    ]
  ]]

  #v(1fr)

  #set text(size: 0.8em)
  _Jacopo Philip Moretti_ #pronouns[he/they]\
  _Marcin Wojnarowski_ #pronouns[he/him]#h(1fr) VSTTE, 14.09.2026
]

== Dataflow Analysis in Kotlin

#one-col[
  Dataflow analysis is generally used for _optimization_:
  #set grid.cell(align: center + horizon)
  #grid(columns: (1fr, 3em, 14em), gutter: 1em)[
    ```kt
    val a = 5
    if (a + 2 == 7) {
      println("It is seven!")
    } else {
      println("Oh no!")
    }
    ```
  ][
  ][
    #h(20em)
  ]
]

== Dataflow Analysis in Kotlin

#one-col[
  Dataflow analysis is generally used for _optimization_:
  #set grid.cell(align: center + horizon)
  #grid(columns: (1fr, 3em, 14em), gutter: 1em)[
    ```kt
    val a = 5
    if (a + 2 == 7) {
      println("It is seven!")
    } else {
      println("Oh no!")
    }
    ```
  ][
    $->$
  ][

    ```kt
    println("It is seven!")
    ```
  ]
]

== Dataflow Analysis in Kotlin

#two-col(columns: (3fr, 1fr))[
  Dataflow analysis for _program validation_?

  ```kt
  fun f(x: Int?): Int {
    if (x != null) {
      // Safe to dereference thanks to the analysis!
      return x + 1
    }
    return 0
  }
  ```
][
  // Type system? 🤨 🤔
]

== Need for formalization

#one-col[
  - Does *nullability analysis* guarantee the lack of _runtime exceptions_?
  #set text(gray)
  - Do *function contracts* properly _approximate_ execution?
  - Are *uniqueness types* _sound_?
]

== Need for formalization

#one-col[
  - Does *nullability analysis* guarantee the lack of _runtime exceptions_?
  - Do *function contracts* properly _approximate_ execution?
  #set text(gray)
  - Are *uniqueness types* _sound_?
]

== Need for formalization

#one-col[
  - Does *nullability analysis* guarantee the lack of _runtime exceptions_?
  - Do *function contracts* properly _approximate_ execution?
  - Are *uniqueness types* _sound_?
]

// == Dataflow Analysis in Kotlin

// #one-col[
// A more involved example:
// ```kt
// fun calculateTax(cost: Double?): Double? {
//   // && is shortcutting...
//   val valid = cost != null && /*(1)*/ cost > 0.0

//   /*2*/

//   Telemetry.log("calculateTax_valid", valid)
//   // ...so if this check passes...
//   if (!valid) return null

//   /*3*/

//   // ...cost can be used without fear!
//   return cost * 0.23
// }
// ```
// ]

= The framework

== The framework

#let coh = $sans("Coh")$
#let coh-def = $coh subset.eq L times S$

#two-col[
  #align(center)[`Chartreux`!]
  - Playground to *specify* and *verify* analyses...

  #set text(fill: gray)

  - ...with *ergonomic* theorems on the analysis result...

  - ...applied to Kotlin constructs for better understanding!
][
  #image("assets/paper-abstract.png")
]

== The framework

#let coh = $sans("Coh")$
#let coh-def = $coh subset.eq L times S$

#two-col[
  #align(center)[`Chartreux`!]
  - Playground to *specify* and *verify* analyses...

  - ...with *ergonomic* theorems on the analysis result...

  #set text(fill: gray)
  - ...applied to Kotlin constructs for better understanding!
][
  #image("assets/paper-abstract.png")
]

== The framework

#let coh = $sans("Coh")$
#let coh-def = $coh subset.eq L times S$

#two-col[
  #align(center)[`Chartreux`!]
  - Playground to *specify* and *verify* analyses...

  - ...with *ergonomic* theorems on the analysis result...

  - ...applied to Kotlin constructs for better understanding!
][
  #image("assets/paper-abstract.png")
]

// == Model

// #two-col[
//   `Chartreux` allows specifying correctness of analyses
//   Abstract interpretation is the art of mimicking execution over _all possible
//   states_, to detect program properties.

//   `Chartreux` allows specifying correctness of analyses, to get guarantees!
// ][
//   #figure(caption: [Semantic preservation of $#coh$])[
//     #image("assets/conc_vs_abs.svg")
//   ]
// ]

// == Correctness

// #one-col[
//   #theorem[
//     For:
//     - a language $L$ with semantics $S$;
//     - and any analysis $A$ that respects them;
//     The result of running $A$ on a program $p$ is correct at _every program point_ of $p$.
//   ]
// ]

// = ALTERNATIVE TO PREVIOUS

/*

== Recipe for a correct analysis

#one-col[
  *Ingredients.*

  - A *language* $L$;
  #set text(fill: gray)
  - An *analysis* $A$;
  - A *proof of coherence* between $A$ and $L$.

  *Result.*
  #theorem(numbered: false)[
    For any $p$, the result of running $A$ on $p$ is correct at
    _every program point_ of $p$.
  ]
]

== Recipe for a correct analysis

#one-col[
  *Ingredients.*

  - A *language* $L$;
  - An *analysis* $A$;
  #set text(fill: gray)
  - A *proof of coherence* between $A$ and $L$.

  *Result.*
  #theorem(numbered: false)[
    For any $p$, the result of running $A$ on $p$ is correct at
    _every program point_ of $p$.
  ]
]

== Recipe for a correct analysis

#one-col[
  *Ingredients.*

  - A *language* $L$;
  - An *analysis* $A$;
  - A *proof of coherence* between $A$ and $L$.

  #set text(fill: gray)
  *Result.*
  #theorem(numbered: false)[
    For any $p$, the result of running $A$ on $p$ is correct at
    _every program point_ of $p$.
  ]
]

== Recipe for a correct analysis

#one-col[
  *Ingredients.*

  - A *language* $L$;
  - An *analysis* $A$;
  - A *proof of coherence* between $A$ and $L$.

  *Result.*
  #theorem(numbered: false)[
    For any $p$, the result of running $A$ on $p$ is correct at
    _every program point_ of $p$.
  ]
]
*/

== Recipe for a correct analysis

#two-col[
  *Ingredients.*
  - A *language* $L$;
  #set text(fill: gray)
  - An *analysis* $A$;
  - A *proof of coherence* between $A$ and $L$.

  *Result.*
  #theorem(numbered: false)[
    The result of running $A$ is correct at _every program point_.
  ]
][
  #figure(caption: [Semantic preservation of $#coh$])[
    #image("assets/conc_vs_abs.svg")
  ]
]

== Recipe for a correct analysis

#two-col[
  *Ingredients.*
  - A *language* $L$;
  - An *analysis* $A$;
  #set text(fill: gray)
  - A *proof of coherence* between $A$ and $L$.

  *Result.*
  #theorem(numbered: false)[
    The result of running $A$ is correct at _every program point_.
  ]
][
  #figure(caption: [Semantic preservation of $#coh$])[
    #image("assets/conc_vs_abs.svg")
  ]
]

== Recipe for a correct analysis

#two-col[
  *Ingredients.*
  - A *language* $L$;
  - An *analysis* $A$;
  - A *proof of coherence* between $A$ and $L$.

  #set text(fill: gray)
  *Result.*
  #theorem(numbered: false)[
    The result of running $A$ is correct at _every program point_.
  ]
][
  #figure(caption: [Semantic preservation of $#coh$])[
    #image("assets/conc_vs_abs.svg")
  ]
]

== Recipe for a correct analysis

#two-col[
  *Ingredients.*
  - A *language* $L$;
  - An *analysis* $A$;
  - A *proof of coherence* between $A$ and $L$.

  *Result.*
  #theorem(numbered: false)[
    The result of running $A$ is correct at _every program point_.
  ]
][
  #figure(caption: [Semantic preservation of $#coh$])[
    #image("assets/conc_vs_abs.svg")
  ]
]

== Correctness, examplified

#two-col[
  ```kt
  fun f(x: Int?): Int {
    if (x != null) {
      // Safe dereference!
      return x + 1
    }
    return 0
  }
  ```
][

]

== Correctness, examplified

#two-col[
  ```kt
  fun f(x: Int?): Int {
    if (x != null) {
      // Safe dereference!
      return x + 1
    }
    return 0
  }
  ```
][
  #figure(caption: [The Control Flow Graph of `f`.])[
    #block(width: 75%)[
      #image("assets/prog_if.png")
    ]
  ]
]

= Application and results

== Nullability with consequents

#two-col(columns: (7fr, 4fr))[
  ```kotlin
  fun calculateTax(cost: Double?): Double? {
    val valid = cost != null && /*1*/cost > 0.0
    /*2*/
    if (!valid) return null
    /*3*/
    return cost * 0.23
  }
  ```
][
  #set text(gray)
  #set raw(theme: none)
  1. ```kotlin cost != null```
  2. ```kotlin valid``` $=>$ ```kotlin cost != null```
  3. ```kotlin valid``` $thick and thick$ ```kotlin valid``` $=>$
    ```kotlin cost != null```
]

== Nullability with consequents

#two-col(columns: (7fr, 4fr))[
  ```kotlin
  fun calculateTax(cost: Double?): Double? {
    val valid = cost != null && /*1*/cost > 0.0
    /*2*/
    if (!valid) return null
    /*3*/
    return cost * 0.23
  }
  ```
][
  1. ```kotlin cost != null```
  #set text(gray)
  #set raw(theme: none)
  2. ```kotlin valid``` $=>$ ```kotlin cost != null```
  3. ```kotlin valid``` $thick and thick$ ```kotlin valid``` $=>$
    ```kotlin cost != null```
]

== Nullability with consequents

#two-col(columns: (7fr, 4fr))[
  ```kotlin
  fun calculateTax(cost: Double?): Double? {
    val valid = cost != null && /*1*/cost > 0.0
    /*2*/
    if (!valid) return null
    /*3*/
    return cost * 0.23
  }
  ```
][
  1. ```kotlin cost != null```
  2. ```kotlin valid``` $=>$ ```kotlin cost != null```
  #set text(gray)
  #set raw(theme: none)
  3. ```kotlin valid``` $thick and thick$ ```kotlin valid``` $=>$
    ```kotlin cost != null```
]

== Nullability with consequents

#two-col(columns: (7fr, 4fr))[
  ```kotlin
  fun calculateTax(cost: Double?): Double? {
    val valid = cost != null && /*1*/cost > 0.0
    /*2*/
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

== Nullability with consequents

#align(center)[
  ```kotlin
  fun calculateTax(cost: Double?): Double? {
    val valid = cost != null && /*1*/cost > 0.0
    /*2*/
    if (!valid) return null
    /*3*/
    return cost * 0.23
  }
  ```
  #show grid.cell: align.with(center)
  #set grid.cell(stroke: 0.1pt, inset: 1em)
  #let diff = underline
  #set text(0.7em)

  #grid(
    columns: (auto,) * 3,
    nullability-lattice($top$, (), `nonnull`, ()),
    nullability-lattice(diff(`nonnull`), (`cost`,), $top$, ()),
    nullability-lattice(`nonnull`, (`cost`,), diff(`nonnull`), ()),

    [1], [2], [3],
  )
]

== Nullability with consequents

#one-col[
  $
    coh_"nullability" (rho, sigma) := forall & x in "Vars"(rho), \
                                             & rho(x) = #raw("nonnull") => \
                                             & sigma(x) != #raw("null")
  $

  #set text(gray)

  #theorem(numbered: false)[
    If the nullability analysis is successful, then the execution of the program
    never gets stuck on `null` values.
  ]
]

== Nullability with consequents

#one-col[
  $
    coh_"nullability" (rho, sigma) := forall & x in "Vars"(rho), \
                                             & rho(x) = #raw("nonnull") => \
                                             & sigma(x) != #raw("null")
  $

  #theorem(numbered: false)[
    If the nullability analysis is successful, then the execution of the program
    never gets stuck on ```kt null``` values.
  ]
]

== Function contracts


#two-col[
  ```kt
  fun run(lam: () -> Unit) {
    // `run` calls `lam` exactly once
    contract {
      callsInplace(lam, EXACTLY_ONCE)
    }
    lam()
  }

  fun main() {
    val x: Int
    run { x = 42 }
    // another safe use of `x`
    println(x + 1)
  }
  ```
  // This result is achieved via special CFG rewrite rules that _assume_ that the
  // functions respect their contracts. Is this correct?
][
  #block(height: 100%, width: 100%)[#align(
    horizon + center,
  )[
    #figure(caption: [
      The CFG for `main`.
    ])[
      #align(center + horizon)[
        #block(inset: 1em)[#image("assets/graph.svg")]
      ]
    ]
  ]]
]

== Function contracts
#one-col[
  #set grid.cell(align: center, inset: 1em)
  #show grid.cell: set text(size: 0.8em)
  #grid(columns: (1fr, 1fr, 1fr))[
    #image("assets/exactly_once.svg", height: 10em)
  ][
    #image("assets/at_least_once.svg", height: 10em)
  ][
    #image("assets/at_most_once.svg", height: 10em)
  ][
    `EXACTLY_ONCE`
  ][
    `AT_LEAST_ONCE`
  ][
    `AT_MOST_ONCE`
  ]
]

== Function contracts

#one-col[
  #theorem(numbered: false)[
    If the counting analysis is successful, then the result of running any
    analysis is correct at _every_ program point.
  ]

  #set text(fill: gray)
  #proof(sketch: true)[
    #align(center)[#block(width: 85%, height: 4em)[
      #image("assets/proofsketch_func.png")
      #place(top + left)[#rect(
        width: 100%,
        height: 100%,
        fill: white.transparentize(36%),
      )]
    ]]
  ]
]

== Function contracts

#one-col[
  #theorem(numbered: false)[
    If the counting analysis is successful, then the result of running any
    analysis is correct at _every_ program point.
  ]

  #proof(sketch: true)[
    #align(center)[#block(width: 85%, height: 4em)[
      #image("assets/proofsketch_func.png")
    ]]
  ]
]

// === Rewrite correctness

// #one-col[
//   #theorem(name: [FTA with functions])[
//     For a _checked_ function family $Phi$, and any program $lan p, Phi ran$, any
//     analysis $A$ on the contract-aware CFG of $p$ satisfies the properties of
//     the _Fundamental Theorem_.
//   ]

//   #proof(sketch: true)[
//     // The analyses are not interprocedural!
//     // Since the lambda
//     // parameter only has access to the caller's execution environment, the
//     // jump is useless from the point of view of the caller.
//     // This means we can define two semantics, with and without jumps,
//     // and relate the two:
//     #v(1em)
//     #figure(caption: [Proof diagram for rewrite correctness])[
//       #image(width: 90%, "assets/func_proof_diagram_hor.svg")
//       #v(0.5em)
//     ]

//     // The jump semantics simulate the regular ones through nondeterministic shenanigans.
//   ]
// ]

= Concluding words

== Where the project stands

#one-col[
  - Implemented generic, verified analysis algorithms;

  #set text(fill: gray)
  - Showed relevance of approach by formalizing current guarantees;

  - Defined clear roadmap for verification of future compiler proposals;
]

== Where the project stands

#one-col[
  - Implemented generic, verified analysis algorithms;

  - Showed relevance of approach by formalizing current guarantees;

  #set text(fill: gray)
  - Defined clear roadmap for verification of future compiler proposals;
]

== Where the project stands

#one-col[
  - Implemented generic, verified analysis algorithms;

  - Showed relevance of approach by formalizing current guarantees;

  - Defined clear roadmap for verification of future compiler proposals;
]

/*
== Future work

#one-col[
  We identify two main direction, intertwined in their goals.

  === For Chartreux

  - More flexible semantics: hard to model arbitrary jumps.
  - More analysis algorithms: beyond Kildall.
  - ...

  === For Kotlin

  - More analyses: flow typing, uniqueness.
  - More language constructs: exceptional control flow.
  - Language correctness: relate the CFG to a Kotlin formalization.
]
*/

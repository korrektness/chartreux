#let _thm-spacing = 1.5em

#let setup-theorems(body) = {
  show figure: it => {
    if type(it.kind) == str and it.kind.starts-with("thm-") {
      block(spacing: _thm-spacing, align(left)[
        *#it.supplement #it.counter.display(it.numbering).* #it.body
      ])
    } else {
      it
    }
  }

  body
}

#let theorem(body, supplement: "Theorem") = figure(
  body,
  kind: "thm-" + supplement,
  supplement: supplement,
  numbering: "1",
)

#let lemma(body) = theorem(body, supplement: "Lemma")
#let definition(body) = theorem(body, supplement: "Definition")

#let proof(body, standalone: false) = block(spacing: 0em)[
  #if not standalone { v(-_thm-spacing) }
  #context v(par.leading)
  _Proof_. #body
  #v(_thm-spacing)
]

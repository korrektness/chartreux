= Duke

Duke is a very simple language which has pure expressions, mutation, conditionals, and loops. We wish to expand it with exceptions:

+ Adding `throw e` statements, where `e` is an arbitrary exception.
+ Adding `try { s1 } catch (x) { s2 }`, where any exception thrown in `try` immediately continues execution in the nearest `catch`. `x` is assigned the value of the thrown expression.

We wish to preserve the CFG construction used in Kotlin, since this is what we want to verify. For `throw e`, no special CFG edges are created. However, during reachability analysis, nodes following a throw as marked as dead (unreachable). We do not yet do reachability analysis. For `try/catch`, two special edges are created: (i) from the start of the `try` to the start of the `catch`, (ii) from the end of the `try` to the start of the `catch`. Additionally, for every assign node in the `try`, we add an edge from it to the start of the `catch`. These extra edges allow us to capture all states of the program even in light of potential interrupts of execution (due to an exception being thrown).

So for the following program:

```js
let a = null
try {
    a = 123
    throw 1 + 2
    print(a + 2)
} catch (x) {
    print(x)
}
```

The CFG is:

#image("cfg.png")

As you notice, there is no edge which connects the throwing of an exception to the appropriate `catch` block. This is an issue, because Chartreux only allows describing concrete semantics which walk along edges. It is not possible to make arbitrary jumps as we it need here.

== Possible solutions

+ We allow language semantics in Chartreux to make arbitrary jumps. This adds an additional obligation on the user to show that doing jumps is safe. I believe this obligation is not a simple one. This also potentially opens up the possibility of the semantics being non-deterministic (we can either take a step along an edge, or do a jump). The advantage of this solution is that this could also potentially model other kotlin features (function calls, non-local returns).
+ Like what was done with function calls, we separate the actual concrete semantics from framework's semantics. Afterwards, we prove that one refines the other. Personally I still don't understand how this works and how it gives us the semantics we want.

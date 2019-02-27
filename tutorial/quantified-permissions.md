# Quantified Permissions #

Viper provides two main mechanisms for specifying permission to a (potentially unbounded) number of heap locations: recursive predicates and *quantified permissions*. While predicates can be a natural choice for modelling entire data structures which are traversed in an orderly top-down fashion, quantified permissions enable point-wise specifications, suitable for modelling heap structures which can be traversed in multiple directions, random-access data structures such as arrays, and unordered data structures such a general graphs.

The basic idea is to allow `acc(e.f)` assertions to occur within a `forall` quantifier. In particular, the `e` receiver expression can be parameterised by the quantified variable, specifying permission to a *set* of different heap locations, one for each instantiation of the quantifier.

As a simple example, we can model a "binary graph" (in which each node has at most two outgoing edges) in the heap, in terms of a set of `nodes`, using the following quantified permission assertion: `forall n:Ref :: { n.first }{ n.second } n in nodes ==> acc(n.first) && acc(n.second)`. Such an assertion provides permission to access the `first` and `second` fields of all nodes `n`. To usefully model a graph, one would typically also require the `nodes` set to be closed under the graph edges, so that a traversal is known to stay within these permissions.

```silver {.runnable }
field first : Ref
field second : Ref

method inc(nodes: Set[Ref], x: Ref)
  requires forall n:Ref :: { n.first } n in nodes ==> 
    acc(n.first) && 
    (n.first != null ==> n.first in nodes)
  requires forall n:Ref :: { n.second } n in nodes ==> 
    acc(n.second) && 
    (n.second != null ==> n.second in nodes)
  requires x in nodes
{
  var y : Ref
  if(x.second != null) {
    y := x.second.first // permissions covered by preconditions
  }
}
```
//exercise//

* Remove the second conjunct from the first precondition. The example should still verify. Now change the field access in the method body to be `x.first.first`. The example will no longer verify, unless you restore the original precondition.
* Try instead making the first precondition `requires forall n:Ref :: n in nodes ==> acc(n.first) && n.first in nodes`. The example should verify. Try adding an assert statement immediately after the assignment: `assert y != null`. This should verify - the modified precondition implicitly guarantees that `n.first` is always non-null (for any `n` in `nodes`), since it provides us with permission to a field of `n.first`. 
* Try restoring the original precondition: `requires forall n:Ref :: n in nodes ==> acc(n.first) && (n.first != null ==> n.first in nodes)`. The `assert` statement that you added in the previous point should no-longer verify, since there is no-longer any reason that `n.first` is guaranteed to be non-null.

///

## Receiver Expressions and Injectivity ##

In the above examples, the receiver expressions used to specify permissions (the `e` expression in `acc(e.f)`) were always the quantified variable itself. This is not a requirement; for example, in the following code, quantified permissions are used along with a function `address` in the `exhale` statement, to exhale permission to multiple field locations:

```silver {.runnable }
field val : Int

function address(i:Int) : Ref
// ensures forall j:Int, k:Int :: j != k ==> address(j)!=address(k)

method test()
{
  inhale acc(address(3).val, 1/2)
  inhale acc(address(2).val, 1/2)
  inhale acc(address(1).val, 1/2)
  exhale forall i:Int :: 1<=i && i<=3 ==> acc(address(i).val, 1/2)
}
```

The expression `address(i)` implicitly defines a mapping between instances `i` of the quantifier and receiver references `address(i)`. Such receiver expressions cannot be fully-general: Viper imposes the restriction that this mapping must be provably <i>injective</i>: for any two instances of such a quantifier, the verifier must be able to prove that the corresponding receiver expressions are different. As usual, this condition can be proven using any information available at the particular program point. In addition, injectivity is only required for instances of the quantifier for which permission is actually required; in the above example, the restriction amounts to showing that the references `address(1)`, `address(2)` and `address(3)` are pairwise unequal. In the following exercises, this is illustrated more thoroughly.

//exercise//

* In the above example, try uncommenting the postcondition (`ensures` line) attached to the `address` function declaration. The complaint about injectivity should then be removed, since the function postcondition guarantees injectivity of `address(i)` as a mapping from `i` to receivers.
* Re-comment out the function postcondition (and check that the error re-occurs). In the example code above, try changing the permission <i>amounts</i> from `1/2` to `1/1` throughout. For example, change `acc(address(1).val,1/2)` to `acc(address(1).val, 1/1)` (or to `acc(address(1).val)`, which has the same meaning. This will remove the complaint about injectivity: the permissions held after the three `inhale` statements are sufficient to guarantee the required inequalities.
* A further alternative is to add instead an additional assumption (somewhere before the `exhale` statement):
 `inhale address(1) != address(2) && address(2) != address(3) && address(3) != address(1)`. Again, this should make the verifier happy; as also shown in the previous point, these inequalities are sufficient for the `exhale` to satisfy the injectivity restriction; there is no requirement for `address(i)` to be injective in general.
///

The injectivity restriction imposed by Viper has the consequence that, when considering permissions required via quantified permissions, one can equivalently think about these per instantiation of the quantified variable, or per corresponding instance of the receiver expression.

## Restrictions ##
<ul>
<li>At present, accessibility predicates are only supported under single quantifiers. Work is ongoing to lift this restriction.</li>
<li>Viper does not currently support Magic Wands under quantifiers.</li>
</ul>




<!--
The precondition of `copyAndInc` requires read permission (`1/2`) to `x1.f` and
*additionally* `write` permission to `x2.f`: the two corresponding
accessibility predicates are combined with the *separating conjunction* `&&`
(denoted by &lowast; in separation logic).
The symbol `&&` is overloaded in Viper: when conjoining accessibility
predicates, it denotes the separating conjunction, otherwise it denotes regular
boolean conjunction.
Multiple pre-/postcondition clauses are implicitly combined with conjunctions:
the first postcondition returns all permissions, the second one states that the
value of `x2.f` after the call will be the old (pre-call) value of `x1.f` plus
one.
In general, nesting an expression `e` in an `old`-expression means that all
heap-dependent subexpressions of `e` are evaluated in the state in which a
method was called.
Note that local variables are not heap-dependent and thus not affected by
`old`.

//exercise//

* Try assigning `x2.f + 1` to `x1.f`. This should fail because the precondition
  only allows reading `x1.f`, not writing to it.
* Change the precondition such that no permissions (`none`) to `x1.f` are
  inhaled. The verification should fail because reading from `x1.f` is only
  permitted if at least some permissions are being held.
* Add an `exhale` statement, as the last line of the body, that exhales half of
  the permissions to `x2.f`. This should cause a verification failure since the
  `write` permission required by the postcondition is no longer available.
* Change the previously added `exhale` statement such that it exhales no
  permissions (`none)`. Afterwards, the verification should succeed again.
* Try implementing a client of `copyAndInc` that inhales `write` permission to
  `x.f` and attempts to call `copyAndInc(x, x)` --- it should fail.
  Why is this not possible with the current specification of `copyAndInc`?
  Can you use an if-then-else assertion of the shape `b ? a1 : a2` (where `b`
  is a `Bool`-typed expression, and `a1` and `a2` are assertions) to change the
  specification of `copyAndInc` such that the client verifies?

///

## Framing ##

Permissions enable the framing of values of heap-dependent expressions across
orthogonal heap changes: since write permission to a heap location `x.f` is
exclusive, a method that holds a non-zero permission fraction to `x.f` can
safely (and modularly) deduce that the value of `x.f` is guaranteed not to
change.

Consider, for example, the previously shown `copyAndInc` method and a client
that invokes it:

```silver {.runnable }
field f: Int

method copyAndInc(x1: Ref, x2:Ref)
  requires acc(x1.f, 1/2) && acc(x2.f)
  ensures  acc(x1.f, 1/2) && acc(x2.f)
  ensures  x2.f == old(x1.f) + 1
{ x2.f := x1.f + 1 }

method client(x1: Ref, x2: Ref)
  requires acc(x1.f) && acc(x2.f)
{
  copyAndInc(x1, x2)
  assert x1.f == old(x1.f) // Succeeds because of framing
}
```

The client's assertion verifies because it holds on to half of the permissions
to `x1.f`; hence, it can modularly conclude that `copyAndInc` does not modify
`x1.f`.

//exercise//

* Change the precondition of the client such that the client inhales only `1/2`
  permission to `x1.f`. The assertion should fail now: since the client
  temporarily lost *all* permission to `x1.f`, it would in general not be sound
  to (modularly) conclude that `copyAndInc` does not modify `x1.f`.
* Try strengthening the postcondition of `copyAndInc` to remidy the situation
  such that the assertion verifies again.

///
-->
# Quantified Permissions

Viper provides two main mechanisms for specifying permission to a (potentially unbounded) number of heap locations: recursive [predicates](./predicates.md) and *quantified permissions*. While predicates can be a natural choice for modelling entire data structures which are traversed in an orderly top-down fashion, quantified permissions enable point-wise specifications, suitable for modelling heap structures which can be traversed in multiple directions, random-access data structures such as arrays, and unordered data structures such as general graphs.

The basic idea is to allow resource assertions such as `acc(e.f)` to occur within the body of a `forall` quantifier. In particular, the `e` receiver expression can be parameterised by the quantified variable, specifying permission to a *set* of different heap locations: one for each instantiation of the quantifier.

As a simple example, we can model a "binary graph" (in which each node has at most two outgoing edges) in the heap, in terms of a set of `nodes`, using the following quantified permission assertion: `forall n:Ref :: { n.first }{ n.second } n in nodes ==> acc(n.first) && acc(n.second)`. Such an assertion provides permission to access the `first` and `second` fields of all nodes `n` (as explained in the [previous section on quantifiers](./quantifiers.md), the `{ n.first }{ n.second }` syntax denotes triggers). To usefully model a graph, one would typically also require the `nodes` set to be closed under the graph edges, so that a traversal is known to stay within these permissions; this is illustrated in the following example:

```viper,editable,playground
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

> **Exercise**
> * Remove the second conjunct from the first precondition. The example should still verify. Now change the field access in the method body to be `x.first.first`. The example will no longer verify, unless you restore the original precondition.
> * Try instead making the first precondition `requires forall n:Ref :: n in nodes ==> acc(n.first) && n.first in nodes`. The example should verify. Try adding an assert statement immediately after the assignment: `assert y != null`. This should verify - the modified precondition implicitly guarantees that `n.first` is always non-null (for any `n` in `nodes`), since it provides us with permission to a field of `n.first`.
> * Try restoring the original precondition: `requires forall n:Ref :: n in nodes ==> acc(n.first) && (n.first != null ==> n.first in nodes)`. The `assert` statement that you added in the previous point should no-longer verify, since there is no-longer any reason that `n.first` is guaranteed to be non-null.

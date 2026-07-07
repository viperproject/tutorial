# Havocking heap locations

Some verification arguments require deliberately *forgetting* the values of heap locations while keeping the permissions to them — for example, to model interference by the environment (say, another thread that may update a shared location), or to encode a non-deterministic update. This can already be expressed with the statements seen so far: exhaling a permission and immediately inhaling it back erases all knowledge about the value of the location, e.g.

```viper
exhale acc(x.f, 1/2)
inhale acc(x.f, 1/2)
```

for a method that holds half permission to `x.f`. Viper provides the `quasihavoc` statement as a more direct way to express this exhale-inhale pattern:

```viper
quasihavoc x.f
```

The two formulations are semantically equivalent; `quasihavoc` exists to allow the backends to implement this common pattern more efficiently, and it is more convenient to write, since it does not mention (and therefore does not depend on) the exact permission amount held: whatever amount of permission to `x.f` the method holds, it is unaffected, and only the knowledge about the location's value is discarded. If no permission to the location is held at all, the statement has no effect.

More generally, a `quasihavoc` statement has the form `quasihavoc b ==> R`, where the resource `R` may be a field access, a predicate instance, or a magic wand, and the optional condition `b` restricts the havoc to the case where `b` is true. Havocking a predicate instance forgets the values of all heap locations folded inside it. There is also a quantified variant, `quasihavocall`, which havocs a resource for all instantiations of a bound variable; like [quantified permissions](./quantified-permissions-injectivity.md), it requires the receiver expression to be injective in the bound variable. The following example demonstrates these forms:

```viper,editable,playground
field f: Int
field g: Int

method fieldHavoc(x: Ref)
  requires acc(x.f, 1/2) && acc(x.g)
  requires x.f == 1 && x.g == 2
{
  quasihavoc x.f
  // the permission is unchanged, so we may still read x.f ...
  var tmp: Int := x.f
  // ... but its value is now unknown, while x.g is unaffected
  assert x.g == 2
}

method conditionalHavoc(x: Ref, b: Bool)
  requires acc(x.f) && x.f == 1
{
  quasihavoc b ==> x.f
  // the value is only forgotten in executions where b is true
  assert !b ==> x.f == 1
}

predicate cell(x: Ref) {
  acc(x.f)
}

method predicateHavoc(x: Ref)
  requires cell(x)
  requires unfolding cell(x) in x.f == 1
{
  // forgets the values of all locations folded inside cell(x)
  quasihavoc cell(x)
  unfold cell(x)
  var tmp: Int := x.f
}

method havocAll(s: Set[Ref])
  requires forall r: Ref :: r in s ==> acc(r.f)
{
  // forgets the values of r.f for all references r in s
  quasihavocall r: Ref :: r in s ==> r.f
}
```

Note that Viper's Verification Condition Generation (VCG) backend currently supports `quasihavoc` only for field and predicate resources (not for magic wands), and does not support `quasihavocall`.

> **Exercise**
> * Add the statement `assert x.f == 1` at the end of `fieldHavoc` and `predicateHavoc`; in both cases, the assertion fails because the value has been forgotten.
> * In `fieldHavoc`, replace `quasihavoc x.f` by the equivalent `exhale acc(x.f, 1/2); inhale acc(x.f, 1/2)` and observe that the behaviour is unchanged. What happens if you instead exhale and inhale the full permission `acc(x.f)`?

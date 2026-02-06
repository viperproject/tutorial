# Termination Measures and `decreases` Clauses

To prove termination of a recursive function, users must specify a termination measure: a Viper expression whose value is checked to decrease at each recursive call, with respect to a well-founded order. Termination measures are provided via *decreases clauses*:

```viper
decreases <tuple>
```

Here, `<tuple>` denotes the termination measure: a tuple of comma-separated expressions. In this tutorial, we interchangeably refer to `<tuple>` as *termination measure* and *decreases tuple*. For functions and methods, a decreases tuple can be defined at the position of a precondition, for a loop, at the position of an invariant.

A common example for termination is the standard `factorial` function, which terminates because its argument decreases with respect to the usual well-founded order over non-negative numbers.

```viper,editable,playground
import <decreases/int.vpr>

function factorial(n:Int) : Int
  requires 0 <= n
  decreases n
{ n == 0 ? 1 : n * factorial(n-1) }
```

Viper successfully verifies that `factorial` terminates: at each recursive invocation, it checks that 1. the termination measure `n` decreases and 2. remains non-negative, i.e. cannot decrease infinitely often. The corresponding well-founded order over non-negative numbers is defined in the file `decreases/int.vpr`, which is part of Viper's standard library.

*Hint*: If you run the Viper verifier Silicon (symbolic-execution-based) with `--printTranslatedProgram` then you can inspect the verification conditions generated for termination checks.

## Predefined Well-Founded Orders {#term_prov_wfo}

Viper's standard library provides definitions of well-founded orders for most types built into Viper, all of which can be imported from the `decreases` folder. The following table lists all provided orders; we write `s1 <_ s2` if `s1` is less than `s2` with respect to the order.

| Build-In Type<br>(file name) | Provided Well-Founded Order |
| ---- | ---- |
|`Ref`<br>(`ref.vpr`)| `r1 <_ r2 <==> r1 == null && r2 != null`
|`Bool`<br>(`bool.vpr`)| `b1 <_ b2 <==> b1 == false && b2 == true`
|`Int`<br>(`int.vpr`)| `i1 <_ i2 <==> i1 < i2 && 0 <= i2`
|`Rational`<br>(`rational.vpr`, rationals will be deprecated in the summer 2023 release):| `r1 <_ r2 <==> r1 <= r2 - 1/1 && 0/1 <= r2`
|`Perm`<br>(`perm.vpr`)| `p1 <_ p2 <==> p1 <= p2 - write && none <= p2`
|`Seq[T]`<br>(`seq.vpr`)| `s1 <_ s2 <==> \|s1\| < \|s2\|`
|`Set[T]`<br>(`set.vpr`)| `s1 <_ s2 <==> \|s1\| < \|s2\|`
|`Multiset[T]`<br>(`multiset.vpr`)| `s1 <_ s2 <==> \|s1\| < \|s2\|`
|`PredicateInstance`<br>(`predicate_instance.vpr`)| `p1 <_ p2 <==> nested(p1, p2)`

All definitions are straightforward, except the last one, which is concerned with using predicate instances as termination measures. Due to the least fixed-point interpretation of predicates, any predicate instance has a finite depth, i.e., can be unfolded only a finite number of times. This implies that a predicate instance `p1`, which is nested inside a predicate instance `p2`, has a smaller (and non-negative) depth than `p2`.

Viper uses this nesting depth to enable termination checks based on predicate instances, as illustrated by the next example, the recursive computation of the length of a linked list: intuitively, the remainder of the linked list, represented by predicate instance `list(this)`, is used as the termination measure. This works because the recursive call is nested under the unfolding of `list(this)`, and takes the smaller predicate instance `list(this.next)`.

```viper,editable,playground
import <decreases/predicate_instance.vpr>

field next: Ref

predicate list(this: Ref) {
  acc(this.next) &&
  (this.next != null ==> list(this.next))
}

function length(this: Ref): Int
  decreases list(this)
  requires list(this)
{
  unfolding list(this) in this.next == null ? 1 : 1 + length(this.next)
}
```

> **Exercise**
>
> Change the body of `length` to just the recursive call `length(this)`. Which error message do you expect?

Final remarks:

* Note that `PredicateInstance` is an internal Viper type, and currently supported only in decreases tuples. The `nested` function is also internal and cannot be used by users.
* For simplicity, all standard well-founded orders can be imported via `decreases/all.vpr`.
* Users can also define [custom well-founded orders](./termination-custom-orders.md).

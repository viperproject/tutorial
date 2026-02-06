# Exclusive Permissions

Permissions to field locations as described so far are exclusive; it is not possible to hold permission to a location more than once. This built-in principle can indirectly guarantee non-aliasing between references: inhaling the assertions `acc(x.f)` and `acc(y.f)` implies `x != y` because otherwise, the *exclusive* permission to `acc(x.f)` would be held twice. This is demonstrated by the following program:

```viper,editable,playground
field f: Int

method exclusivity(x: Ref, y: Ref) {
  inhale acc(x.f)
  inhale acc(y.f)
  exhale x != y
}
```

> **Exercise**
> * Comment one of the two inhale statements. Does the exhale statement still succeed?
> * Add the third inhale statement `inhale x == y` anywhere before the exhale statement and change the latter to `exhale false`. Can false be asserted? Why does this demonstrate that it is not possible to hold more than one exclusive permission to `x.f`?

In Viper, accessibility predicates can be conjoined via `&&`; the resulting assertion requires the _sum_ of the permissions required by its two conjuncts. Therefore, the two statements `inhale acc(x.f); inhale acc(y.f)` (semicolons are required in Viper only if statements are on the same line) are equivalent to the single statement `inhale acc(x.f) && acc(y.f)`. In both cases, the obtained permissions imply that `x` and `y` cannot be aliases.
Intuitively, the statement `inhale acc(x.f) && acc(y.f)` can be understood as inhaling permission to `acc(x.f)`, and in *addition* to that, inhaling the permission to `acc(y.f)`. Technically, this conjunction between resource assertions is strongly related to the *separating conjunction* from [separation logic](https://link.springer.com/chapter/10.1007/3-540-44802-0_1); formal details of the connection (and how to encode standard separation logic into Viper) can be found in [this paper](https://lmcs.episciences.org/802).

<!--**TODO: maybe consider also a link to wikipedia (for separation logic and separating conjunction), as suggested in one of the feedback e-mails **.-->

<!--**TODO: We could add a note here that briefly states that a conjunction between non-resource assertions, or a resource and a non-resource assertion, is the usual boolean conjunction. However, my feeling is that such a note will be more confusing then helpful.** -->

We can now see how exclusive permissions enable framing and modular verification, as illustrated by the next example below. Here, method `client` is able to frame the property `b.f == 3` across the call to `inc(a, 3)` because holding permission to both `a.f` and `b.f` implies that `a` and `b` cannot be aliases, and because method `inc`'s specification states that `inc` only requires the permission to `a.f`. Since permission to `b.f` is _retained_, the value of `b.f` can be framed across the method call. Informally, and thinking more operationally, the method would not be able to modify this field location, since it lacks the necessary permission to do so.

```viper,editable,playground
field f: Int

method inc(x: Ref, i: Int)
  requires acc(x.f)
  ensures  acc(x.f)
  ensures  x.f == old(x.f) + i
{
  x.f := x.f + i
}

method client(a: Ref, b: Ref) {
  inhale acc(a.f) && acc(b.f)

  a.f := 1
  b.f := 3

  inc(a, 3)

  assert b.f == 3
}
```

Note:

* The expression `old(x.f)` in method `inc`'s postcondition denotes the value that `x.f` had at the beginning of the method call. In general, an *old expression* `old(e)` causes all heap-dependent subexpressions of `e` (in particular, field accesses and calls to heap-dependent functions) to be evaluated in the initial state of the corresponding method call. Note that variables are not heap-dependent; their values are unaffected by `old`.
* Method specifications can contain multiple `requires` and `ensures` clauses; this has the same meaning as if all `requires` assertions were conjoined, and likewise for `ensures`.

> **Exercise**
> * Add the statement `assert a.f == 4` to the end of method `client`; it will verify. Comment the second postcondition of `inc` to make it fail. What happens if you comment the first (but not the second) postcondition?
> * Add a method `copyAndInc(x: Ref, y: Ref)` with the implementation `x.f := y.f + 1`. Can you give it a specification such that, when invoked as `copyAndInc(a, b)` by method `client` in place of the call `inc(a, 3)`, the statement `assert b.f == 3 && a.f == 4` in method `client` verifies?
> * In method `client`, change the invocation of method `copyAndInc` to `copyAndInc(a, a)`, and change the `assert` statement to `assert b.f == 3 && a.f == 2`. You'll probably have to change the specifications of method `copyAndInc` to verify the new code.

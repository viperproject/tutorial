# Conditional Termination

We previously presented three different kinds of termination measures: a tuple `e1, e2, ...`, wildcard (`_`) for "just assume that something is decreased", and star (`*`) for "no termination guarantees". It may sometimes be desirable to combine different measures, e.g., in order to reduce proof efforts by providing a concrete decreases tuple for certain invocations only, complemented with wildcard for the remaining invocations.

To account for this, Viper supports *conditional termination* clauses for the first two  kinds of measures (tuple, wildcard):

```viper
decreases <tuple> ... if <condition>
decreases _ if <condition>
```

Here, `<condition>` is a boolean expression under which the decreases clause is considered. Omitting the condition, as in all previous examples, is equivalent to `if true`. Consequently, the condition `false` is equivalent to not providing the decreases clause at all.

> **Note**
>
> To ensure soundness, only a *single* clause per kind of measure is allowed. Moreover, it is not allowed to "downgrade" from a tuple to a wildcard: if `<tuple>`'s condition held in the call's prestate, then `<tuple>` must decrease, even if the wildcard condition holds at a recursive call.

The following example illustrates combined conditional termination clauses: function `sign` promises to decrease `x` if positive, and something (wildcard) if `x` is negative. In case `x` is zero, function `sign` does not (promise to) terminate.

```viper,editable,playground
import <decreases/int.vpr>

function sign(x: Int): Int
  decreases x if 1 <= x
  decreases _ if x <= -1
  decreases * // can also simply be omitted
{
  x == 0 ? sign(x) :
  1 < x  ? sign(x - 1) :
  x < -1 ? sign(x + 1) :
           x
}

function caller(x: Int): Int
  decreases // must terminate
{
  sign(x)
}
```

> **Exercise**
> * Function `caller` does not verify. Why is that?
> * Strengthen function `caller`'s specification to make it verify.

We refer to the condition `1 <= x` of the clause `decreases x if 1 <= x` as the *tuple condition*, and to the condition `x <= -1` of the clause `decreases _ if x <= -1` as the *wildcard condition*. The disjunction of the two, i.e. `1 <= x || x <= -1`, is the *termination condition*: the effective condition under which the function (promises to) terminate.

When verifying termination of function `sign`, the following happens for the recursive invocations:

* `sign(x)`: the termination check is vacuous because the invocation happens under the condition `x == 0`, for which `sign` does not promise to terminate.
* `sign(x - 1)`: termination measure `x` is checked to decrease, since the call happens under the condition `1 < x` (which implies that the tuple condition held in the prestate).
* `sign(x + 1)`: the termination check is again vacuous because the call happens under the condition `x < -1`, which is the wildcard condition and termination is therefore assumed.

When verifying termination of function `caller`, the termination condition (`1 <= x || x <= -1`) of function `sign` is checked. Since it might not hold, a verification error is reported.

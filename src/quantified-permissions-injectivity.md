# Receiver Expressions and Injectivity

In the above examples, the receiver expressions used to specify permissions (the `e` expression in `acc(e.f)`) were always the quantified variable itself. This is not a requirement; for example, in the following code, quantified permissions are used along with a function `address` in the `exhale` statement, to exhale permission to multiple field locations:

```viper,editable,playground
field val: Int

function address(i: Int): Ref
//   ensures inverse(result) == i

// function inverse(r: Ref): Int
//   ensures address(result) == r

method test()
{
  inhale acc(address(3).val, 1/2)
  inhale acc(address(2).val, 1/2)
  inhale acc(address(1).val, 1/2)
  exhale forall i: Int :: 1 <= i <= 3 ==> acc(address(i).val, 1/2)
}
```

The expression `address(i)` implicitly defines a mapping between instances `i` of the quantifier and receiver references `address(i)`. Such receiver expressions cannot be fully-general: Viper imposes the restriction that this mapping must be provably *injective*: for any two instances of such a quantifier, the verifier must be able to prove that the corresponding receiver expressions are different. For us, this means proving `forall j: Int, k: Int :: j != k ==> address(j) != address(k)`. As usual, this condition can be proven using any information available at the particular program point. In addition, injectivity is only required for instances of the quantifier for which permission is actually required; in the above example, the restriction amounts to showing that the references `address(1)`, `address(2)` and `address(3)` are pairwise unequal. In the following exercises, this is illustrated more thoroughly.

> **Exercise**
> * In the above example, try uncommenting the three lines after the `address` function declaration. The complaint about injectivity should then be removed, since the existence of an inverse function proves injectivity of `address`.
> * Re-comment out the three lines (and check that the error re-occurs). In the example code above, try changing the permission <i>amounts</i> from `1/2` to `1/1` throughout. For example, change `acc(address(1).val,1/2)` to `acc(address(1).val, 1/1)` (or to `acc(address(1).val)`, which has the same meaning. This will remove the complaint about injectivity: the permissions held after the three `inhale` statements are sufficient to guarantee the required inequalities.
> * A further alternative is to add instead an additional assumption (somewhere before the `exhale` statement):
 `inhale address(1) != address(2) && address(2) != address(3) && address(3) != address(1)`. Again, this should make the verifier happy; as also shown in the previous point, these inequalities are sufficient for the `exhale` to satisfy the injectivity restriction; there is no requirement for `address(i)` to be injective in general.

The injectivity restriction imposed by Viper has the consequence that, when considering permissions required via quantified permissions, one can equivalently think about these per instantiation of the quantified variable, or per corresponding instance of the receiver expression.

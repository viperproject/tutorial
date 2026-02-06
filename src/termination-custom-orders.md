# Custom Well-Founded Orders

As previously mentioned, Viper offers [predefined orders](./termination-measures.html#term_prov_wfo) for its built-in types, plus predicates. However, via [domains](./domains.md), Viper also enables users to define their own types. In order to use values of custom types as termination measures, users can either define a mapping from custom to some built-in type, or they can directly define a well-founded order over the custom type.

In the remainder of this subsection, both approaches will be illustrated using a combination of the `MyInt` example (from the earlier subsection on domains) and a `factorial` function operating on `MyInt`. In the example below, the destructor `get` is used to map a `MyInt` to a regular `Int`, which indirectly allows using `MyInt` in the function's decreases clause.

```viper,editable,playground
import <decreases/int.vpr>

domain MyInt {
  function put(i: Int): MyInt   // Constructor
  function get(m: MyInt): Int   // Destructor
  function dec(m: MyInt): MyInt // Decrement by one

  axiom { forall i: Int   :: {put(i)} get(put(i)) == i }
  axiom { forall m: MyInt :: {dec(m)} dec(m) == put(get(m) - 1) }
}

function factorial(m: MyInt): Int
  requires 0 <= get(m)
  decreases get(m)
{ get(m) == 0 ? 1 : get(m) * factorial(dec(m)) }
```

Alternatively, a well-founded order for `MyInt` itself can be defined, by instantiating the two special functions `decreasing` and `bounded` for `MyInt`. The necessary function declarations are provided by the standard library file `decreases/declaration.vpr`, and look as follows:

```viper
domain WellFoundedOrder[T] {
  // v1 is less than v2
  function decreasing(v1: T, v2: T): Bool

  // v is bounded
  function bounded(v: T): Bool
}
```

Function `decreasing` is used to define an order between two values `v1` and `v2` of a custom type `T`, whereas function `bounded` is used to define a lower bound on such values. Suitable definitions for both suffices to establish a well-founded order (where, as before, `<_` denotes well-founded less-than over type `T`):

```plain
v1 <_ v2 <==> decreasing(v1, v2) && bounded(v2)
```

The necessary properties of `decreasing` and `bounded` for values of type `T` can be defined via axioms. For the `MyInt` type from before, suitable axioms would be:

```viper
domain MyIntWellFoundedOrder {
  axiom {
    forall i1: MyInt, i2: MyInt :: {decreasing(i1, i2)}
      get(i1) < get(i2) <==> decreasing(i1, i2)
  }
  axiom {
    forall m: MyInt :: {bounded(m)}
      0 <= get(m) <==> bounded(m)
  }
}
```

> **Note**
>
> The functions `decreasing` and `bounded` must be declared by the Viper program to verify, which is easiest done by importing `decreases/declaration.vpr`. This is also what the predefined orders, e.g., `decreases/int.vpr`, do.

> **Exercise**
> * Change the `factorial` function in the program above such that parameter `m` is used as its termination measure. The termination check should then fail because no well-founded order for `MyInt` has been defined.
> * Add the axioms for `decreasing` and `bounded`, to define a well-founded order for `MyInt` values. The program should verify again.

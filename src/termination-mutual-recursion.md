# Mutual Recursion

For mutually recursive functions, Viper implements the following approach (as, e.g., [Dafny](https://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf) does as well): given a mutually recursive function `fun`, Viper verifies that `fun` function's termination measure decreases at each *indirectly* recursive call. By transitivity, this implies that the measure decreased by the time a recursive invocation of `fun` takes place.

A simple case of mutual recursion is illustrated next, by functions `is_even` and `is_odd`:

```viper,editable,playground
import <decreases/int.vpr>

function is_even(x: Int): Bool
  requires x >= 0
  decreases x
{
  x == 0 ? true : is_odd(x-1)
}

function is_odd(y: Int): Bool
  requires y >= 0
  decreases y
{
  y == 0 ? false : is_even(y-1)
}
```

Consider function `is_even`: its termination measure `x` decreases at the indirectly recursive call `is_odd(x-1)`, where `is_odd`'s termination measure `y` is instantiated with `x-1`. Analogously, `is_odd`'s termination measure decreases at the call `is_even(y-1)`.

In the example above, the two termination measures are tuples of equal length and type. However, this is not required of mutually recursive functions in order to prove their termination. Consider the next example (which verifies successfully):

```viper,editable,playground
import <decreases/int.vpr>
import <decreases/bool.vpr>

function fun1(y: Int, b: Bool): Int
  decreases y, b
{
    (b     ? fun1(y, false) : 1)
  + (y > 0 ? fun2(y-1)      : 2)
}

function fun2(x: Int): Int
  decreases x
{
  x > 0 ? fun1(x-1, true) : 3
}
```

At indirectly recursive calls, two decreases tuples are compared by lexicographical order of their longest commonly typed prefix (as does, e.g., Dafny). E.g., for the indirectly recursive call `fun2(y-1)` in function `fun1`, Viper verifies that `y-1 <_ y`, while for the recursive call `fun1(y, false)`, it verifies that `y <_ y || (y == y && false <_ b)`.

> **Exercise**
> * In the above example, change the call `fun1(x-1, true)` to `fun1(x, true)` -- the program still verifies. That's because Viper appends a `Top` element (an internal value of any type, larger than any other value) to each tuple, a neat trick also implemented by, e.g., Dafny and F*. Can you explain how this helps with checking termination of the call `fun1(x, true)`?

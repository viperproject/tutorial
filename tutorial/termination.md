# Termination

Viper provides the possibility to prove termination of recursive functions and methods as well as termination of while loops. Because most of the following presented concepts work the same for recursive function as for recursive methods or loops, the case of recursive functions is used to describe them. Differences are described in the sections on [methods](#term_methods) and on [loops](#term_loops).

To prove termination of a recursive function a user must define a termination measure. This termination measure is then checked to decrease in each iteration (with respect to a well-founded order).
If no termination measure is defined, Viper won't check termination.

Termination measures can be defined in the *decreases clause*.

```silver
decreases [exp]
```
Here, `[exp]` is a tuple of comma-separated expressions which is the termination measure. Henceforth, we refer to such a decreases clause also as *decreases tuple*.

For a function or a method the decreases tuple can be defined at the position of the preconditions, for a loop at the position of the invariants.

A simple example is the standard `factorial` function, which is terminating because the parameter n decreases with respect to the usual well-founded order over positive numbers.

```silver {.runnable}
import <decreases/int.vpr>

function factorial(n:Int) : Int
  requires 0 <= n
  decreases n
{ n == 0 ? 1 : n * factorial(n-1) }
```

Viper verifies successfully that the termination measure `n` decreases in each recursive invocation of itself and always is positive when the function recursively invokes itself. The well-founded order over positive numbers is defined in the file `decreases/int.vpr`, which is provided by Viper and can be imported with `import <decreases/int.vpr>` (more information in [section on provided well-founded orders](#prov_wfo)).

### Provided Well-Founded Orders {#term_prov_wfo}

Viper provides files with definitions of well-founded orders for build-in types in the folder `decreases` (we write `s1 <_ s2` if `s1` is after `s2` with respect to a well founded order).

| Build-In Type<br>(file name) | Provided Well-Founded Order |
| ---- | ---- |
|`Ref`<br>(`ref.vpr`)| `r1 <_ r2 <==> r1 == null && r2 != null`
|`Bool`<br>(`bool.vpr`)| `b1 <_ b2 <==> b1 == false && b2 == true`
|`Int`<br>(`int.vpr`)| `i1 <_ i2 <==> i1 < i2 && 0 <= i2`
|`Rational`<br>(`rational.vpr`):| `r1 <_ r2 <==> r1 <= r2 - 1/1 && 0/1 <= r2`
|`Perm`<br>(`perm.vpr`)| `p1 <_ p2 <==> p1 <= p2 - write && none <= p2`
|`Seq[T]`<br>(`seq.vpr`)| `s1 <_ s2 <==> |s1| < |s2|`
|`Set[T]`<br>(`set.vpr`)| `s1 <_ s2 <==> |s1| < |s2|`
|`Multiset[T]`<br>(`multiset.vpr`)| `s1 <_ s2 <==> |s1| < |s2|`

Another well-founded order can be defined on predicate instances. Due to the least fixpoint interpretation of predicates, any predicate instance has a finite depth of predicates (the number of nested folded predicate instances). This implies that a predicate instance `p1`, which is nested inside a predicate instance `p2`, has a smaller but still a non-negative depth of predicates than `p2`. Viper provides therefore also the following definition of a well-founded order over predicate instances:

| Type<br>(file name) | Provided Well-Founded Order |
| ---- | ---- |
|`PredicateInstance`<br>(`predicate_instance.vpr`)| `p1 <_ p2 <==> nested(p1, p2)`

It is important to note, that `PredicateInstance` is not a build-in type and is currently only supported in decreases tuples as termination measure. Also the `nested` function is not a build-in function and cannot be used by the user.
Usually for recursive function, a predicate instance can be used as a termination measure if the recursive call is inside an unfolding expression. The `listLength` function, which recursively calls itself inside an unfolding expression, is such a function.

```silver {.runnable}
import <decreases/predicate_instance.vpr>

field elem: Int
field next: Ref

predicate list(this: Ref) {
  acc(this.elem) && acc(this.next) &&
  (this.next != null ==> list(this.next))
}

function listLength(l:Ref) : Int
  decreases list(l)
  requires list(l)
  ensures  result > 0
{ 
  unfolding list(l) in l.next == null ? 1 : 1 + listLength(l.next) 
}
```

If all provided well-founded orders are required, the file `decreases/all.vpr` can be imported.

How well-founded orders can be defined is explained later in this chapter.

## Tuple

In the examples given above, the termination measures were always single expressions. This approach works easily for many cases, but sometimes it can be difficult to find a single expression which decreases well-founded in each iteration. Viper, therefore, allows a tuple of expressions to be defined as termination measure. The expressions of the tuple are then considered in lexicographical order.

More precisely, Viper defines the well-founded order over tuples as follows:
Let `[a1, a2, ...]` and `[b1, b2, ...]` be two non-empty tuples of finite size.

`[a1, a2, ...] <_ [b1, b2, ...] <==> a1 <_ b1 || (a1 == b1 && [a2, ...] <_ [b2, ...])`

All other cases, i.e. in cases in which at least one of the tuples is empty, are equivalent to false.

`[...] <_ [...] <==> false`


A function for which normally a tuple as termination measure is used to prove termination is the Ackermann function.

```silver {.runnable}
import <decreases/int.vpr>

function ack(m:Int, n:Int):Int
decreases m,n
requires m >= 0
requires n >= 0
ensures result >= 0
{
  m==0 ? n+1 :
    n==0 ?
      ack(m-1,1) :
      ack(m-1, ack(m, n-1))
}
```

For the first recursive call `ack(m-1,1)` and the second recursive call `ack(m-1, ack(m, n-1))` the first expression of the tuple (i.e. `m`) decreases, hence, the other part of the tuple is not required to decrease. In the third and nested recursive call `ack(m, n-1)` the first expression of the tuple stays unchanged while the second expression (i.e. `n`) decreases.

The well-founded order over tuples must not be imported. However, the well-founded orders of the types appearing in the tuple still must be.

## Decreases Wildcard

In a function for which Viper checks termination, i.e. for which a termination measure is defined, any function call must also terminate. Functions without a termination measure are considered as possibly non-terminating functions. Because of that any function directly or indirectly invoked by another function for which a termination measure is defined also a termination measure must be provided. This can become cumbersome if termination of some functions can be assumed or really difficult in other cases.

Therefore, Viper allows to define functions for which termination can be assumed but is not checked by Viper. This is accomplished by providing a *decreases wildcard* instead of a decreases tuple.

```silver
decreases _
```

## Decreases *

As previously mentioned, if no decreases tuple or decreases wildcard is provided possible non-termination is assumed by Viper. A user can also make this explicit by providing a *decreases star* as decreases clause.

```silver
decreases *
```

However, using a decreases star has no affect on the verification done by Viper and is equivalent to providing no decreases clause at all.


## Define Well-Founded Order

So far in the presented examples, only build-in types (and predicate instances) were used in the termination measures. For each of these types a file provided by Viper had to be imported, which defined a well-founded order for it.
To be able to use some additionally defined type as a termination measure either a function mapping to a build-in type has to be used or a well-founded order on the additional type has to be defined. Using one example we will show the first approach and then present the second approach.

For brevity, the already presented `MyInteger` type is used as the additionally defined type and the standard `factorial` function, which in this case requires a `MyInteger` as argument instead of the build-in type `Int`.
Since the standard `factorial` function invokes itself recursively with a by 1 decreased integer, the function `dec` was defined, which expects a `MyInteger` as argument and returns a by 1 decreased `MyInteger`. The function `get_value` is used in the termination measure to map `MyInteger` values to the build-in type `Int`, such that the well-founded order over `Int` can be used to check termination.

```silver {.runnable}
import <decreases/int.vpr>

domain MyInteger {
  function create_int(x: Int): MyInteger
  function get_value(a: MyInteger): Int
  function dec(a: MyInteger): MyInteger

  axiom axDec {
    forall a: MyInteger ::
      dec(a) == create_int( get_value(a) - 1 )
  }
}

function factorial(n:MyInteger) : Int
  requires 0 <= n
  decreases get_value(n)
{ n == 0 ? 1 : n * factorial(dec(n)) }
```

A well-founded orders over Viper types are defined using the two functions `decreasing` and `bounded`. These are declared in the provided file `decreases/declaration.vpr`:
```silver
domain WellFoundedOrder[T]{
  // arg1 is smaller then arg2
  function decreasing(arg1:T, arg2:T):Bool

  // arg is bounded
  function bounded(arg:T):Bool
}
```
While the `decreasing` function is used to define an order between elements, the `bounded` function is used to define a lower bound on the elements. Combining both a well-founded order is defined. For two expressions `e1` and `e2` of some type `T` a well-founded order is defined as follows (using the previously introduced fictive well-founded decreasing operator `<_`):

`e1 <_ e2 <==> decreasing(e1, e2) && bounded(e2)`

To define properties to the function `decreasing` and `bounded` axioms have to be used. For the example from above the following axioms define a well-founded order over `MyInteger`.

```silver
domain MyIntegerWellFoundedOrder{
  axiom MyInteger_ax_dec{
    forall int1: MyInteger, int2: MyInteger :: {decreasing(int1, int2)}
      get_value(int1) < get_value(int2) <==> decreasing(int1, int2)
  }
  axiom integer_ax_bound{
    forall int: MyInteger :: {bounded(int)}
      get_value(int) >= 0 <==> bounded(int)
  }
}
```

It is important to note that the functions `decreasing` and `bounded` have to be declared in the Viper program, which is easiest done by importing `decreases/declaration.vpr`.
All of the provided well-founded orders also import the file `decreases/declaration.vpr`.

//exercise//
* In the above example, use the parameter `n` as the termination measure for the `factorial` function. The termination check should then fail because no well-founded order for `MyInteger` has been defined.
* Add the axioms which provide a definition of a well-founded order for `MyInteger` to the example. The termination error should then be removed.
///

## Methods {#term_methods}
For a method the decreases clauses can be defined at the position of the preconditions (same as for functions).
When a termination measure is provided for a method, Viper checks that the termination measure decreases in each directly or indirectly recursive invocation with respect to a well-founded order. Further, any other invocated method as well as loops defined in the method are checked to terminate.

## Loops {#term_loops}
While loops expect their decreases clauses to be defined at the position of the invariants.
When a termination measure is defined for a while loop, Viper will check that this termination measure will be decreased in any following iteration of the loop.
A successful verification implies that for any execution a finite unrolling of the loop exists.

As an example we use the `sum` method. For the loop `n-i` can be used as termination measure since it decreases between any consecutive iteration of the loop.
```silver {.runnable}
import <decreases/int.vpr>

method sum(n: Int) returns (res: Int)
  requires 0 <= n
  ensures  res == n * (n + 1) / 2
{
  res := 0
  var i: Int := 0;
  while(i <= n)
    invariant i <= (n + 1)
    invariant res == (i - 1) * i / 2
    decreases n-i
  {
    res := res + i
    i := i + 1
  }
}
```

## Partial Termination

_Note: this section introduces an extension to the decreases clauses presented above, which some users may wish to skip over for the moment._

In many cases termination should be proven (or assumed) in any possible execution. However, this might not always be the case and termination should only be proven (or assumed) under certain conditions.
Such condition can be provided after decreases clauses.

```silver
decreases [exp] if [condition]
```

```silver
decreases _ if [condition]
```

`[condition]` is a boolean expression under which the decreases clause is considered. The condition `true` is equivalent to the decreases clause without any condition (as shown in the examples above). The condition `false` is equivalent to not providing the decreases clause.

The following example shows a method which terminates if it is invoked with a non-negative `x`. This can be proven by using `x` as termination measure under the condition `x >= 0`.
Additionally, the method is defined with a decreases wildcard under the condition `x < 0`.

```silver {.runnable}
import <decreases/int.vpr>

method m(x: Int)
  decreases x if x >= 0
  decreases _ if x < 0
{
  if (x >= 0){
    if (x != 0){
      m(x-1)
    }
  }else{
    var y: Int
    m(y)
  }
}
```

We introduce now the concept of the *termination specification*. For each function, method or loop, a termination specifications encapsulate the specified decreases clauses. Each termination specification is defined by at most one decreases tuple and one decreases wildcard. The condition of the decreases tuple defines the *tuple condition*. The disjunction of the conditions of the decreases tuple and the decreases wildcard defines the *termination condition*.

For the method `m` from the example above, the tuple condition is `x >= 0` and the termination condition is `x >= 0 || x < 0`, which is equivalent to `true`.
Assuming the tuple condition, for each recursive invocation it is checked that in the following iteration the tuple condition still will be satisfied and that the termination measure (here `x`) will decreases.

In other words, the tuple condition defines the states in which the termination measure definitely decreases with respect to a well-founded order.
The termination condition is checked to be satisfied if termination is required, e.g. when another method for which termination must be proven invokes `m`.

## Mutually Recursive Functions and Effective Termination Measure

Functions (or methods) can also be indirectly recursive via other functions (or methods, respectively). An example of such mutually recursive functions are the `is_even` and `is_odd` function shown in the next example.

```silver {.runnable}
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

Viper verifies in this case that the termination measure decreases in the indirectly recursive function calls. E.g. in the function `is_even` the termination measure is `x` and the function call `is_odd(x-1)` decreases it because the termination measure of `is_odd` is `y` (i.e. `x-1`). Similar is the case for the function `is_odd`.

In the given example the two termination measures are of the same size and also equally typed. However, this is not required of mutually recursive functions/methods to be able to prove their termination. This can be seen in the following example of two mutually recursive methods.

```silver {.runnable}
import <decreases/int.vpr>

method m1(y: Int, b: Bool)
  decreases y, b
{
  if (b){
    m1(y, false)
  }

  if (y > 0) {
    m2(y-1)
  }
}

method m2(x: Int)
  decreases x
{
  if (x > 0){
    m1(x-1, true)
  }
}
```

At indirectly recursive calls, two termination measure, i.e. tuples, are compared by lexicographical order of their longest commonly typed prefix (This approach is also used in Dafny [https://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf], however, this might change if Viper is gonna allow to define well-founded orders between different types). For the indirectly recursive method call `m2(x-1)` in the method `m1` Viper verifies that `y-1 <_ y`, while for the recursive call `m1(y, false)` it is verified that `y <_ y || (y == y && false <_ b)`.


The effective termination measure used by Viper actually is the user's provided tuple appended with a `Top` element. The `Top` element does not exist in Viper but is considered to be of any Viper type and bigger than any Viper value. This allows the user sometimes to define a more simple termination measure.
(Similar approaches are also used in Dafny as well as in F*)

//exercise//
* In the above example, change the method call `m1(x-1, true)` in the method `m2` to `m1(x, true)`. Viper then checks for this particular method call that `x <_ x || (x == x && true <_ Top)` which verifies successfully because `true <_ Top` is always assumed to be true.
///



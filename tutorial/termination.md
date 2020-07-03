# Termination {#termination}

In the context of Viper, reasoning about termination serves (at least) two purposes: the first is to prove that code terminates, i.e. total correctness, the second is to indirectly prove that Viper functions are *well-defined*. The second aspect is crucial even for front-ends that are not concerned with total correctness, because specifications, often expressed via Viper's pure functions, would be meaningless if the involved functions were not well-defined.

Front-ends can encode their own termination proofs, but since proving termination is a crucial verification task with subtle pitfalls, Viper has support for termination proofs built-in, based on the well-known approach of *termination measures* (ranking functions).

//note//
By default, i.e. if no termination measure is specified, then Viper won't check termination. This can be useful, e.g. if a front-end already performs or encodes its own termination checks.
///

In this section, we will introduce Viper's support for termination proofs: first, we describe how to specify termination measures, then we explain termination proofs for (mutually) recursive functions. Lastly, we discuss our *experimental* support for termination of methods and loops. **[TODO: Add forward links]**

## Termination Measures and Decreases Clauses

To prove termination of a recursive function, users must specify a termination measure: a Viper expression whose value is checked to decrease at each recursive call, with respect to a well-founded order. Termination measures are provided via *decreases clauses*:

```silver
decreases M
```

Here, `M` denotes the termination measure: a tuple of comma-separated expressions. In this tutorial, we interchangeably refer to `M` as *termination measure* and *decreases tuple*.
For functions and methods, a decreases tuple can be defined in the position of a precondition, for a loop, in the position of an invariant.

A common example for termination is the standard `factorial` function, which terminates because its argument decreases with respect to the usual well-founded order over non-negative numbers.

```silver {.runnable}
import <decreases/int.vpr>

function factorial(n:Int) : Int
  requires 0 <= n
  decreases n
{ n == 0 ? 1 : n * factorial(n-1) }
```

Viper successfully verifies that `factorial` terminates: at each recursive invocation, it checks that 1. the termination measure `n` decreases and 2. remains non-negative, i.e. cannot decrease infinitely often. The corresponding well-founded order over non-negative numbers is defined in the file `decreases/int.vpr`, which is part of Viper's standard library.

### Predefined Well-Founded Orders {#term_prov_wfo}

Viper's standard library provides definitions of well-founded orders for most types built into Viper, all of which can be imported from the `decreases` folder. The following table lists all provided orders; we write `s1 <_ s2` if `s1` is after `s2` with respect to the order.

| Build-In Type<br>(file name) | Provided Well-Founded Order |
| ---- | ---- |
|`Ref`<br>(`ref.vpr`)| `r1 <_ r2 <==> r1 == null && r2 != null`
|`Bool`<br>(`bool.vpr`)| `b1 <_ b2 <==> b1 == false && b2 == true`
|`Int`<br>(`int.vpr`)| `i1 <_ i2 <==> i1 < i2 && 0 <= i2`
|`Rational`<br>(`rational.vpr`):| `r1 <_ r2 <==> r1 <= r2 - 1/1 && 0/1 <= r2`
|`Perm`<br>(`perm.vpr`)| `p1 <_ p2 <==> p1 <= p2 - write && none <= p2`
|`Seq[T]`<br>(`seq.vpr`)| `s1 <_ s2 <==> \|s1\| < \|s2\|`
|`Set[T]`<br>(`set.vpr`)| `s1 <_ s2 <==> \|s1\| < \|s2\|`
|`Multiset[T]`<br>(`multiset.vpr`)| `s1 <_ s2 <==> \|s1\| < \|s2\|`
|`PredicateInstance`<br>(`predicate_instance.vpr`)| `p1 <_ p2 <==> nested(p1, p2)`

All definitions are straight-forward, except the last one, which is concerned with using predicate instances as termination measures. Due to the least fixed-point interpretation of predicates, any predicate instance has a finite depth, i.e. can be unfolded only a finite number of times. This implies that a predicate instance `p1`, which is nested inside a predicate instance `p2`, has a smaller (and non-negative) depth than `p2`.

Viper uses this to enable termination checks based on predicate instances, as illustrated by the next example, the recursive computation of the length of a linked list: intuitively, the remainder of the linked list, represented by predicate instance `list(this)`, is used as the termination measure. This works because the recursive call is nested under the unfolding of `list(this)`, and takes the smaller predicate instance `list(this.next)`.

```silver {.runnable}
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

//exercise//
Change the body of `length` to just the recursive call `length(this)`. Which error message do you expect?
///

Final remarks:

* Note that `PredicateInstance` is an internal Viper type, and currently only supported in decreases tuples. The `nested` function is also internal and cannot be used by users.
* For simplicity, all standard well-founded orders can be imported via `decreases/all.vpr`.
* Users can define custom well-founded orders, as explained in **[TODO: forward link]**.

## General Syntax of Decreases Tuples

In the previous examples, the termination measures were always single expressions. It is often difficult, however, to find a single expression whose value decreases at each all, and Viper therefore also supports tuples of expressions as termination measures. The well-founded order for tuples is the lexicographical order over the tuple elements.

More precisely, let `[a1, a2, ...]` and `[b1, b2, ...]` be two non-empty tuples of finite (and for now, equal) length, then the well-founded order `<_` that is used to compare the two tuples is defined as follows:

```plain
[a1, a2, ...] <_ [b1, b2, ...]
  <==>
a1 <_ b1 || (a1 == b1 && [a2, ...] <_ [b2, ...])
```

Special cases, such as empty tuples, tuples of different length and tuples of different types will be discussed later.

A typical example of a function for which a tuple as termination measure is used, is the Ackermann function:

```silver {.runnable}
import <decreases/int.vpr>

function ack(m:Int, n:Int):Int
  decreases m, n
  requires m >= 0
  requires n >= 0
  ensures result >= 0
{
  m == 0 ? n + 1 :
  n == 0 ? ack(m - 1, 1) :
           ack(m - 1, ack(m, n - 1))
}
```

For the first recursive call `ack(m - 1, 1)`, and the second (outer) recursive call `ack(m - 1, ack(m, n - 1))`, the first expression of the tuple (i.e. `m`) decreases. Hence, the other part of the tuple is not required to decrease in this situation. In the third (inner) recursive call `ack(m, n - 1)` the first expression of the tuple is unchanged, while the second tuple expression (i.e. `n`) decreases.

//exercise//
Swap the tuple elements, i.e. change the decreases clause to `n, m`. For which of the recursive calls do you expect error messages?
///

The well-founded order over tuples must not be imported (and cannot be customised). However, the well-founded orders of the types appearing in the tuple must be.

## Special Decreases Tuples

Viper supports three decreases tuples whose semantics require further explanation.

### Empty

Consider the following pair of functions, where `compute` performs the actual computation and `facade` merely provides a default argument to `compute`:

```silver
function facade(i: Int): Int { compute(i, 0) }

function compute(i: Int, j: Int): Int { i + j }
```

Both functions have no decreases clause, and Viper thus won't generate termination checks. This may be fine now, since the functions obviously terminate, but if `compute` were changed to be recursive, potential non-termination might go unnoticed. To account for future code changes, users could use "artificial" constants as termination measures, but Viper offers a better solution: to ensure termination checks, users can specify empty tuples, and Viper's call-graph analysis (performed to detect mutual recursion **[TODO: forward link]**) effectively infers suitable constants.

```silver {.runnable}
function facade(i: Int): Int
  decreases
{ compute(i, 0) }

function compute(i: Int, j: Int): Int
  decreases
{ i + j }
```

//exercise//

* Make the body of `compute` recursive, e.g. by changing it to `i <= 0 ? j : compute(i - 1, j + i)`, and verify the program
* Provide a termination measure, so that the changed program verifies again

///

### Wildcard

Specifying a termination measure might not always be an option: It could be too cumbersome to express it in Viper; it could be considered a problem to deal with later; or it could be that the function does not terminate in an operational sense, but is nevertheless well-defined. Simply omitting the decreases clause, however, might not be an option, e.g. because the function is called from another function, for which termination checks are generated.

For such cases, Viper offers the *wildcard* measure `_`, which expresses that a function is to be considered terminating, although no termination checks are generated. I.e. it is effectively a free assumption.

```silver {.runnable}
function collatz(n: Int): Int
  requires 1 <= n
  decreases _ // I can't be bothered right now
{
  n == 1     ? n :
  n % 2 == 0 ? collatz(n / 2) :
               collatz(3 * n + 1)
}
```

### Star

To explicate that a function is not checked for termination, and may thus not terminate, Viper supports the *star* measure `*`. This special measure has no affect on the verification performed by Viper, and is equivalent to providing no decreases clause at all.

```silver {.runnable}
function nonterm(): Int
  decreases * // Whole clause could as well have been omitted
{ 1 + nonterm() }
```

## Custom Well-Founded Orders

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



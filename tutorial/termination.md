# Termination {#termination}

In the context of Viper, reasoning about termination serves (at least) two purposes: the first is to prove that methods and loops terminate, the second is to ensure that Viper functions are *well-defined*. The second aspect is crucial even for front-ends that are not concerned with total correctness, because specifications, often expressed via Viper's pure functions, would be meaningless if the involved functions were not well-defined.

Front-ends can encode their own termination proofs, but since proving termination is a crucial verification task with subtle pitfalls, Viper has support for termination proofs built in, based on the well-known approach of *termination measures* (ranking functions).

//note//
By default, i.e. if no termination measure is specified, then Viper won't check termination. This can be useful, e.g. if a front-end already performs or encodes its own termination checks.
///

In this section, we will introduce Viper's support for termination proofs: first, we describe how to specify termination measures, then we explain termination proofs for (mutually) recursive functions. Lastly, we discuss our *experimental* support for termination of [methods and loops](#term_statements).

## Termination Measures and Decreases Clauses

To prove termination of a recursive function, users must specify a termination measure: a Viper expression whose value is checked to decrease at each recursive call, with respect to a well-founded order. Termination measures are provided via *decreases clauses*:

```silver
decreases <tuple>
```

Here, `<tuple>` denotes the termination measure: a tuple of comma-separated expressions. In this tutorial, we interchangeably refer to `<tuple>` as *termination measure* and *decreases tuple*. For functions and methods, a decreases tuple can be defined at the position of a precondition, for a loop, at the position of an invariant.

A common example for termination is the standard `factorial` function, which terminates because its argument decreases with respect to the usual well-founded order over non-negative numbers.

```silver {.runnable}
import <decreases/int.vpr>

function factorial(n:Int) : Int
  requires 0 <= n
  decreases n
{ n == 0 ? 1 : n * factorial(n-1) }
```

Viper successfully verifies that `factorial` terminates: at each recursive invocation, it checks that 1. the termination measure `n` decreases and 2. remains non-negative, i.e. cannot decrease infinitely often. The corresponding well-founded order over non-negative numbers is defined in the file `decreases/int.vpr`, which is part of Viper's standard library.

*Hint*: If you run the Viper verifier Silicon (symbolic-execution-based) with `--printTranslatedProgram` then you can inspect the verification conditions generated for termination checks.

### Predefined Well-Founded Orders {#term_prov_wfo}

Viper's standard library provides definitions of well-founded orders for most types built into Viper, all of which can be imported from the `decreases` folder. The following table lists all provided orders; we write `s1 <_ s2` if `s1` is less than `s2` with respect to the order.

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

All definitions are straightforward, except the last one, which is concerned with using predicate instances as termination measures. Due to the least fixed-point interpretation of predicates, any predicate instance has a finite depth, i.e., can be unfolded only a finite number of times. This implies that a predicate instance `p1`, which is nested inside a predicate instance `p2`, has a smaller (and non-negative) depth than `p2`.

Viper uses this nesting depth to enable termination checks based on predicate instances, as illustrated by the next example, the recursive computation of the length of a linked list: intuitively, the remainder of the linked list, represented by predicate instance `list(this)`, is used as the termination measure. This works because the recursive call is nested under the unfolding of `list(this)`, and takes the smaller predicate instance `list(this.next)`.

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

* Note that `PredicateInstance` is an internal Viper type, and currently supported only in decreases tuples. The `nested` function is also internal and cannot be used by users.
* For simplicity, all standard well-founded orders can be imported via `decreases/all.vpr`.
* Users can also define [custom well-founded orders](#term_custom_orders).

## General Syntax of Decreases Tuples

In the previous examples, the termination measures were always single expressions. However, it is not always possible to find a single expression whose value decreases at each call, and Viper therefore also supports tuples of expressions as termination measures. The well-founded order for tuples is the lexicographical order over the tuple elements.

More precisely, let `(a1, a2, ...)` and `(b1, b2, ...)` be two non-empty tuples of finite (and for now, equal) length. The well-founded order `<_` that is used to compare the two tuples is defined as follows:

```plain
(a1, a2, ...) <_ (b1, b2, ...)
    <==>
a1 <_ b1  ||  a1 == b1 && (a2, ...) <_ (b2, ...) 
```

Special cases, such as empty tuples, tuples of different length, and tuples of different types will be discussed later.

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

For the first recursive call `ack(m - 1, 1)`, and the second (outer) recursive call `ack(m - 1, ack(m, n - 1))`, the first expression of the tuple (i.e. `m`) decreases. Hence, the other part of the tuple is not required to decrease in this situation. In the third (inner) recursive call `ack(m, n - 1)` the first expression of the tuple is unchanged, while the second tuple expression (i.e., `n`) decreases.

//exercise//
Swap the tuple elements, i.e., change the decreases clause to `n, m`. For which of the recursive calls do you expect error messages?
///

The well-founded order over tuples need not be imported (and cannot be customised). However, the well-founded orders of the types appearing in the tuple must be.

## Special Decreases Tuples

Viper supports three decreases tuples whose semantics require further explanation.

### Empty {#term_empty_tuple}

Consider the following pair of functions, where `compute` performs the actual computation and `facade` merely provides a default argument to `compute`:

```silver
function facade(i: Int): Int { compute(i, 0) }

function compute(i: Int, j: Int): Int { i + j }
```

Both functions have no decreases clause, and Viper thus won't generate termination checks. This may be fine now, since the functions obviously terminate, but if `compute` were changed to be recursive, potential non-termination might go unnoticed. To account for future code changes, users could use "artificial" constants as termination measures, but Viper offers a better solution: to ensure termination checks, users can specify empty tuples, and Viper's call-graph analysis (performed to detect [mutual recursion](#term_mut_rec)) effectively infers suitable constants.

```silver {.runnable}
function facade(i: Int): Int
  decreases
{ compute(i, 0) }

function compute(i: Int, j: Int): Int
  decreases
{ i + j }
```

//exercise//

* Make the body of `compute` recursive, e.g., by changing it to `i <= 0 ? j : compute(i - 1, j + i)`, and verify the program
* Provide a termination measure, so that the changed program verifies again

///

### Wildcard

Specifying a termination measure might not always be an option: it could be too cumbersome to express; it could be considered a problem to deal with later; or it could be that the function does not terminate in an operational sense, but is nevertheless well-defined. Simply omitting the decreases clause, however, might not be an option, e.g. because the function is called from another function, for which termination checks are generated.

For such cases, Viper offers the *wildcard* measure `_`, which expresses that a function is to be considered terminating, although no termination checks are generated. I.e., a wildcard measure is effectively an unchecked assumption.

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

To explicate that a function is not checked for termination, and may thus not terminate, Viper supports the *star* measure `*`. This special measure is equivalent to providing no decreases clause at all, but may be useful for documenation purposes.

```silver {.runnable}
function nonterm(): Int
  decreases * // Whole clause could as well have been omitted
{ 1 + nonterm() }
```

## Custom Well-Founded Orders {#term_custom_orders}

As previously mentioned, Viper offers [predefined orders](#term_prov_wfo) for its built-in types, plus predicates. However, via [domains](#domains), Viper also enables users to define their own types. In order to use values of custom types as termination measures, users can either define a mapping from custom to some built-in type, or they can directly define a well-founded order over the custom type.

In the remainder of this subsection, both approaches will be illustrated using a combination of the `MyInt` example (from the earlier subsection on domains) and a `factorial` function operating on `MyInt`. In the example below, the destructor `get` is used to map a `MyInt` to a regular `Int`, which indirectly allows using `MyInt` in the function's decreases clause.

```silver {.runnable}
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

```silver
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

```silver
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

//note//
The functions `decreasing` and `bounded` must be declared by the Viper program to verify, which is easiest done by importing `decreases/declaration.vpr`. This is also what the predefined orders, e.g., `decreases/int.vpr`, do.
///

//exercise//

* Change the `factorial` function in the program above such that parameter `m` is used as its termination measure. The termination check should then fail because no well-founded order for `MyInt` has been defined.
* Add the axioms for `decreasing` and `bounded`, to define a well-founded order for `MyInt` values. The program should verify again.

///

## Mutual Recursion {#term_mut_rec}

For mutually recursive functions, Viper implements the following approach (as, e.g., [Dafny](https://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf) does as well): given a mutually recursive function `fun`, Viper verifies that `fun` function's termination measure decreases at each *indirectly* recursive call. By transitivity, this implies that the measure decreased by the time a recursive invocation of `fun` takes place.

A simple case of mutual recursion is illustrated next, by functions `is_even` and `is_odd`:

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

Consider function `is_even`: its termination measure `x` decreases at the indirectly recursive call `is_odd(x-1)`, where `is_odd`'s termination measure `y` is instantiated with `x-1`. Analogously, `is_odd`'s termination measure decreases at the call `is_even(y-1)`.

In the example above, the two termination measures are tuples of equal length and type. However, this is not required of mutually recursive functions in order to prove their termination. Consider the next example (which verifies successfully):

```silver {.runnable}
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

//exercise//

* Comment the import of `bool.vpr`, and reverify the program. Can you explain the resulting verification error?

* In the above example, change the call `fun1(x-1, true)` to `fun1(x, true)` -- the program still verifies. That's because Viper appends a `Top` element (an internal value of any type, larger than any other value) to each tuple, a neat trick also implemented by, e.g., Dafny and F*. Can you explain how this helps with checking termination of the call `fun1(x, true)`?

///

## Conditional Termination

We previously presented three different kinds of termination measures: a tuple `e1, e2, ...`, wildcard (`_`) for "just assume that something is decreased", and star (`*`) for "no termination guarantees". It may sometimes be desirable to combine different measures, e.g., in order to reduce proof efforts by providing a concrete decreases tuple for certain invocations only, complemented with wildcard for the remaining invocations.

To account for this, Viper supports *conditional termination* clauses for the first two  kinds of measures (tuple, wildcard):

```silver
decreases <tuple> ... if <condition>
decreases _ if <condition>
```

Here, `<condition>` is a boolean expression under which the decreases clause is considered. Omitting the condition, as in all previous examples, is equivalent to `if true`. Consequently, the condition `false` is equivalent to not providing the decreases clause at all.

//note//
To ensure soundness, only a *single* clause per kind of measure is allowed. Moreover, it is not allowed to "downgrade" from a tuple to a wildcard: if `<tuple>`'s condition held in the call's prestate, then `<tuple>` must decrease, even if the wildcard condition holds at a recursive call.
///

The following example illustrates combined conditional termination clauses: function `sign` promises to decrease `x` if positive, and something (wildcard) if `x` is negative. In case `x` is zero, function `sign` does not (promise to) terminate.

```silver {.runnable}
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

//exercise//

* Function `caller` does not verify. Why is that?
* Strengthen function `caller`'s specification to make it verify.

///

We refer to the condition `1 <= x` of the clause `decreases x if 1 <= x` as the *tuple condition*, and to the condition `x <= -1` of the clause `decreases _ if x <= -1` as the *wildcard condition*. The disjunction of the two, i.e. `1 <= x || x <= -1`, is the *termination condition*: the effective condition under which the function (promises to) terminate.

When verifying termination of function `sign`, the following happens for the recursive invocations:

* `sign(x)`: the termination check is vacuous because the invocation happens under the condition `x == 0`, for which `sign` does not promise to terminate.
* `sign(x - 1)`: termination measure `x` is checked to decrease, since the call happens under the condition `1 < x` (which implies that the tuple condition held in the prestate).
* `sign(x + 1)`: the termination check is again vacuous because the call happens under the condition `x < -1`, which is the wildcard condition and termination is therefore assumed.

When verifying termination of function `caller`, the termination condition (`1 <= x || x <= -1`) of function `sign` is checked. Since it might not hold, a verification error is reported.

## Abstract Functions

Termination specifications may also be provided for abstract functions, i.e., those without a body. For such functions, Viper still checks that the specifications are well-defined, which includes that pre- and postconditions terminate. Moreover, when an abstract function is invoked, the previously described call-site checks are made.

When Viper performs a call-graph analysis to determine (mutually) recursive functions, abstract functions are assumed to not (mutually) recurse through their omitted bodies.

## Statement Termination (Experimental) {#term_statements}

//warning//

Termination checks outside of functions -- for methods and loops, and method and function calls -- are considered experimental: their semantics could change in the future, or they might be removed from Viper completely.

We encourage you to experiment with the current implementation, and to let us know if it suits your needs and whether changes or additional features would benefit your verification efforts, etc.
///

### Function Calls inside Methods {#term_fct_calls}

The development of the *experimental* termination checks for statements was (partly) guided by Viper's intended use as an intermediate verification language. This shaped, among other things, how function calls are currently handled.

Front-ends may use Viper functions to encode (pure) program procedures, but front-ends may also use functions to encode proof-relevant properties. Similarly, Viper methods may be used to encode (impure) program procedures, or to encode proof lemmas. Moreover, encoded program procedures could contain Viper statements corresponding to actual statements from the source program, interspersed with Viper statements that encode additional proof steps.

Consider, e.g., a Viper function `elems(ll)` that denotes the set of all elements in a potentially cyclic linked-list `ll`. A statement such as `inhale es == elems(ll)` could be part of a sequence of program statements -- in which case `elems(ll)` should probably terminate -- or it could be an additional proof step, in which case it would suffice if `elems(ll)` were well-defined.

**Function calls inside Viper methods (as opposed to calls inside functions) are therefore (currently) not checked for termination**, and front-ends would have to generate appropriate checks where necessary. Potential alternatives include (1) to always check termination -- probably too restrictive; (2) to enable users to specify termination requirements at call-site, e.g. via attributes/annotations -- but the latter are currently not available in Viper.

### Checking Loop Termination {#term_loops}

Viper `while` loops accept decreases clauses at the position of invariants, as illustrated by the following code snippet:

```silver
while (0 < i)
  decreases i
{
  i := i - 1
}
```

Given such a specification, Viper will check that the termination measure decreases if the loop body is executed again. **A successful verification then implies that the loop is always bounded, i.e. that a finite unrolling of the loop exists**. Consequently, Viper does (currently) not check that each statement, including nested loops, in the loop body terminates, as illustrated by the next code snippet:

```silver
method m() // might not terminate

while (0 < i)
  decreases i // verifies successfully (finite unrolling exists)
{
  i := i - 1
  m()
  while (true) {}
}
```

We have chosen this approach for the following reasons (but are happy to receive feedback and discuss alternatives):

* Minimality: Interpreting loop termination as "a finite unrolling exists" can be seen as the weakest reasonable requirement, compared to the stronger (additional) requirement of all body statements having to terminate (note: the same argument does not apply to functions).

* Uniformity: When proving method termination (discussed next), the current approach directly exhibits the same behaviour for both syntactic `while` loops and loops encoded via `goto`s and `label`s (but see the note below). If loop bodies had to terminate as well, it would pose the question of which statements belonged to a goto-loop, which in general cannot be answered unambiguously (e.g. when inferring a while-loop from a goto-loop). This uniformity also extends to manually unrolled loops, as some front-ends might do.

* Expressiveness: If loop body termination checks are required, they can be encoded easily (potentially via a synthetic method that only hosts the loop body). 

* Familiarity: The same approach is used in Dafny (but then again, Dafny was not designed as an intermediate verification language)

### Checking Method Termination {#term_methods}

The currently implemented approach to checking termination of methods is similar to the previously described approach for functions: decreases clauses can be specified at the position of preconditions; if provided, **Viper checks that the termination measure decreases in each directly or indirectly recursive method invocation, and that other method calls, as well as loops, terminate**. As [previous described](#term_fct_calls), *function* applications inside methods are *not* checked for termination.

A straightforward example is method `sum`, shown next:

```silver {.runnable}
import <decreases/int.vpr>

method sum(n: Int) returns (res: Int)
  requires 0 <= n
  decreases
  ensures res == n * (n + 1) / 2
{
  res := 0
  var i: Int := 0;

  while (i <= n)
    invariant i <= (n + 1)
    invariant res == (i - 1) * i / 2
    decreases n-i
  {
    res := res + i
    i := i + 1
  }
}
```

//exercise//

* Remove the decreases-clause from the loop and observe that the method no longer verifies.
* Revert to the initial program, add declaration `method m()` to the program, and call `m` inside the loop. Observe that it is (again) the method that fails to verify now.
* Avoid the error by removing the decreases-clause from method `sum` (or by adding a wildcard decreases-clause to method `m`).
* Revert to the initial program, add a nested loop, e.g. `var j: Int := n; while(0 < j) { j := j - 1 }`, and observe the resulting verification failure. Experiment a bit with adding new and removing existing decreases clauses.

///

Final remark: Viper (currently) performs a call-graph analysis for methods to detect mutually recursive methods. Analogous to [the case of functions](#term_empty_tuple), this is done for convenience, to unburden users from having to write "artificial" constant termination measures for non-recursive methods. This could be considered a deviation from Viper's otherwise method-modular verification approach -- please let us know if this poses a problem in your use case of Viper.

# Functions

Just as predicates can be used to define parameterised (and potentially-recursive) assertions, Viper *functions* define parameterised and potentially-recursive *expressions*. A function can have any number of parameters, and always returns a single value; evaluation of a Viper function (just as any other Viper expression) is side-effect free. Function applications may occur both in code and in specifications: anywhere that Viper expressions may occur.

Functions are introduced in top-level declarations of the form:

```silver
function f(...): T
  requires A
  ensures  E1
{ E2 }
```

or

```silver
function f(...): T
  requires A
  ensures  E1
```

where `f` is a globally-unique function name, followed by a possibly-empty list of parameters, and a result type `T`. Functions may have an arbitrary number of pre- and postconditions; each precondition (indicated by the `requires` keyword) consists of an assertion `A`, whereas each postcondition (indicated by the `ensures` keyword) consists of an expression `E1`. That is, preconditions may contain resource assertions such as accessibility predicates, but postconditions must not (this difference from methods reflects the fact that function applications are side-effect-free, and so the pre- and post-states of a function application are the same; one can think of function preconditions as also being implicit additional postconditions). The result of the function is referred to using the keyword `result` in postconditions.

The following example defines a function `listLength` that takes a null-terminated simply-linked list and computes its length. As shown in the body of `listLength`, function applications are written simply as the function name followed by appropriately-typed arguments in parentheses. The precondition of `listLength` expresses the fact that the function application can only be evaluated when the corresponding `list` predicate instance is held, while the post-condition expresses the fact that the length of a list is always a non-negative integer.

```silver {.runnable}
field elem: Int
field next: Ref

predicate list(this: Ref) {
  acc(this.elem) && acc(this.next) &&
  (this.next != null ==> list(this.next))
}

function listLength(l:Ref) : Int
  requires list(l)
  ensures  result > 0
{ 
  unfolding list(l) in l.next == null ? 1 : 1 + listLength(l.next) 
}
```

The function body declaration `{ E2 }` (if provided) must contain an expression `E2` of (return) type `T`; it may contain function invocations, including recursive invocations of `f` itself. Function declarations of the latter form (that is, without a function body) introduce abstract functions, which may be useful for information hiding reasons, or to model functions which need not or cannot be directly implemented, e.g., because they model externally-justified information about the encoded program (such as the behaviour of library code). The following example illustrates this by adding a `capacity` function, intended to model a capacity suitable for storing the elements of the list in an array-like container.

```silver
function capacity(l:Ref): Int
  requires list(l)
  ensures  listLength(l) <= result && result <= 2 * listLength(l)
```

Note that functions declared in [Viper domains (i.e. *domain functions*)](#domains) are considered by Viper to be abstract state-independent total functions. As such, they can neither have a body nor be equipped with any pre-/postconditions; see the [domains section](#domains) for more details. In contrast, top-level functions can be state-dependent; the ability for function preconditions to include permissions allows them to depend on not only the values of their parameters, but also on heap locations to which their preconditions require permissions.

Viper checks that the function body and any postconditions are framed by the preconditions; that is, the preconditions must require all permissions that are needed to evaluate the function body and the postconditions. Moreover, Viper verifies that the postconditions can be proven to hold for the result of the function. At present, Viper does *not* check that function definitions necessarily terminate (though this feature is planned to be added soon); Viper users should take care that their function definitions guarantee termination (at least in states in which the function precondition holds). As the checking of a recursive function definition is essentially a proof by induction on the unrolling of the definition, not checking termination can readily lead to unsound behaviour. The following example yields such an inconsistency by means of a non-terminating function:

```silver {.runnable}
function bad() : Int
  ensures 0 == 1
{ bad() }
```

Due to the least fixpoint interpretation of [predicates](#predicates), any recursive function whose recursive calls occur inside an `unfolding` expression are guaranteed to be terminating, as in the case of the `listLength` function above. Another standard termination checking technique is to ensure that some well-founded measure on the function parameter values decreases for each recursive function application. This idea can in fact be seen to subsume the `unfolding` case above, if one considers the depth of predicates (the number of nested folded predicate instances) as the termination measure.

An example of a terminating function not based on predicates is the standard `factorial` function, which is terminating because the parameter `n` decreases with respect to the usual well-founded order over positive numbers.

```silver {.runnable}
function factorial(n:Int) : Int
  requires 0 <= n
{ n == 0 ? 1 : n * factorial(n-1) }
```

For non-abstract functions, Viper reasons about function applications in terms of the function bodies. That is, in contrast to methods, it is not always necessary to provide a postcondition in order to convey
information to the caller of a function. Nevertheless, postconditions are useful for abstract functions and in situations where the property expressed in the postcondition does not directly follow from unfolding the function body once but, for instance, requires induction. In the case of the `listLength` function, the non-negativity of the result is indeed an inductive property, and is not exploitable by Viper unless stated in the postcondition. 

For every function *application*, Viper checks that the function precondition is true in the current state, and then assumes the value of the function application to be equal to the function body (if provided), as well as assuming any postconditions. Fully expanding function bodies cannot work for recursive functions. Instead, functions are by-default expanded only once; additional expansions are triggered when unfolding or folding a predicate that is mentioned in the function's preconditions. This feature allows one to traverse recursive structures and simultaneously reason about the permissions and values. For example, since predicate `list` was mentioned in the precondition of function `listLength` earlier, the body of any function call `listLength(l)` is unfolded whenever a predicate `list(l)` is. This is why the following implementation of the `capacity` function can be successfully verified:

```silver
function capacity(l:Ref): Int
  requires list(l)
  ensures  listLength(l) <= result && result <= 2 * listLength(l)
{ unfolding list(l) in l.next == null
  ? 1
  : unfolding list(l.next) in l.next.next == null
  ? 2
  : 3 + capacity(l.next.next) }
```

The example below is an alternative version of the previously shown
list segment example from the [predicates section](#predicates): instead of using a predicate parameter for the
abstract representation of the list segment (as a mathematical
sequence), a function is introduced that computes the abstraction. This usage of functions to eliminate  predicate parameters which are redundant (in the sense that their values can instead be computed given any predicate instance and its other parameters) is common in Viper.

```silver {.runnable }
field elem: Int
field next: Ref

predicate lseg(this: Ref, last: Ref) {
  this != last ==>
    acc(this.elem) && acc(this.next) &&
    this.next != null &&
    lseg(this.next, last)
}

function values(this: Ref, last: Ref): Seq[Int]
  requires lseg(this, last)
{
  unfolding lseg(this, last) in 
    this == last
      ? Seq[Int]()
      : Seq(this.elem) ++ values(this.next, last)
}

method removeFirst(this: Ref, last: Ref) returns (first: Int, rest: Ref)
  requires lseg(this, last)
  requires this != last
  ensures  lseg(rest, last)
  ensures  values(rest, last) == old(values(this, last)[1..])
{
  unfold lseg(this, last)

  first := this.elem
  rest := this.next
}
```

The `values` function requires an `lseg` predicate instance in its precondition to obtain the permissions to traverse the list. Its body uses an `unfolding` expression to obtain the predicate instance required for the recursive application.

//exercise//

* Use the `values` function to strengthen the postcondition of `removeFirst` by stating that `first` was indeed the first element of the segment.
* Extend the example by a `contains` function that checks whether or not a list segment contains a given element.
* Extend the example by implementing an `append` method that appends an element to a list segment
  (similar to the one used in the predicate section). Afterwards:
  * Use `contains` to express that the appended element is contained in the resulting segment.
  * Alternatively, use `values` to express that: (1) the given an element has been appended and (2) that the values stored in the rest of the list segment have not been changed.

///

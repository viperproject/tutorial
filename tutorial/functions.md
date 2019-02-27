# Functions

Just as predicates can be used to define parameterised (and potentially-recursive) assertions, Viper *functions* define parameterised and potentially-recursive *expressions*. A function can have any number of parameters, and always returns a single value; evaluation of a Viper function (just as any other Viper expression) is side-effect free. Function can be called both in code and in specifications; anywhere that Viper expressions may occur.

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

where `f` is a globally-unique function name, followed by a possibly-empty list of parameters, and a result type `T`. Functions may have an arbitrary number of pre- and postconditions; each precondition (indicated by the `requires` keyword) consists of an assertion `A`, whereas each postcondition (indicated by the  `ensures` keyword) consists of an expression `E1`. That is, preconditions may contain resource assertions such as accessibility predicates, but postconditions must not.

The function body `E2` (if provided) must be an expression of (return) type `T`; it may contain function invocations, including recursive invocations of `f` itself. Function declarations of the latter form (that is, without a function body) introduce abstract functions, which may be useful for information hiding reasons, or to model functions which need not or cannot be directly implemented, e.g., because they model externally-justified information about the encoded program (such as the behaviour of library code).

Viper checks that the function body and the postconditions are framed by the preconditions; that is, the preconditions must require all permissions that are needed to evaluate the function body and the postconditions. Moreover, Viper verifies that the postconditions hold for the result of the function (the keyword `result` is used in postcondition to refer to the result of the function). At present, Viper does *not* check that function definitions necessarily terminate (though this feature is planned to be added soon); Viper users should take care that their function definitions guarantee termination (at least in states in which the function precondition holds).

For non-abstract functions, Viper reasons about function applications in terms of the function bodies. That is, in contrast to methods, it is not always necessary to provide postcondition in order to convey
information to the caller of a function. Nevertheless, postconditions are useful for abstract functions and in situations where the property expressed in the postcondition does not directly follow from the function body (but, for instance, requires induction). Postconditions will be checked to be guaranteed by the function definition in any state in which the function precondition holds; for recursively-defined functions, this check is effectively an induction proof on the definition of the function itself (which is one reason why function termination is important).

For every function *application*, Viper checks that the function precondition is true in the current state, and then assumes the value of the function application to be equal to the function body (if provided), as well as assuming any postconditions. Fully expanding function bodies cannnot work for recursive functions. Such functions are by-default expanded only once; additional expansions are triggered when unfolding or folding a predicate that is mentioned in the function preconditions. This feature allows one to traverse recursive structures and simultaneously reason about the permissions and values.

The example below is an alternative version of the previously shown
list segment example: instead of using a predicate parameter for the
abstract representation of the list segment (as a mathematical
sequence), a function is introduced that computes the abstraction.

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


<!---
The example below adds a `contains` function to the list example.
The precondition provides permissions to access all list nodes.

```silver {.runnable }
field elem: Int
field next: Ref

predicate list(this: Ref) {
  acc(this.elem) && acc(this.next) &&
  (this.next != null ==> acc(list(this.next)))
}

function contains(this: Ref, e: Int): Bool
  requires acc(list(this))
{
  unfolding acc(list(this)) in
    this.elem == e ? true : (this.next == null ? false : contains(this.next, e))
}
```

**Things to try**

* Extend the example by a `contents` function that yields the sequence of
  integers contained in the list

* Extend the `append` method form the predicates section with a
  postcondition that ensures that `e` is contained in the list

* Using the `contents` function, extend the `append` method
  form the predicates section with a postcondition that specifies how
  the contents of the list change
-->
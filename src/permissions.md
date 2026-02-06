# Permissions

Reasoning about the heap of a Viper program is governed by *field permissions*, which specify the heap locations that a statement, an expression or an assertion may access (read and/or modify).
Heap locations can be accessed only if the corresponding permission is *held* by the currently verified method. The simplest form of field permission is the *exclusive* permission to a heap location `x.f`; it expresses that the current method may read and write to the location, whereas other methods or threads are not allowed to access it in any way.

Every Viper operation, i.e., every statement, expression, or assertion, has an implicit or explicit specification expressing which field permissions the operation requires, i.e., which locations it accesses. The part of the heap denoted this way is called the *footprint* of an operation.
Permissions enable preserving information about heap values in Viper: as long as the footprint of an expression is disjoint from the footprint of a method call, it can be concluded that the call does not change the expression's value, even if the concrete method implementation is unknown. Preserving properties this way is called *framing*: e.g. we might say that the value of an expression is *framed* across a method call, or in general, across a statement.
For example: the footprints of the expression `x.f == 0` and the field assignment statement `x.f := 1` are not disjoint, and the property `x.f == 0` can therefore not be framed across the assignment. In contrast, the property could be framed across `y.f := 0` if `y` and `x` were known to not be aliases. Permissions can also be used to guarantee non-aliasing, as will be discussed in more detail [later](./permissions-fractional.md).

In pre- and postconditions, and generally in assertions, permission to a field is denoted by an *accessibility predicate*: an assertion which is written `acc(x.f)`. An accessibility predicate in a method's precondition can be understood as an obligation for a caller to *transfer* the permission to the callee, thereby giving it up. Consequently, an accessibility predicate in a postcondition can be understood as a permission transfer in the opposite direction: from callee to caller.

A simple example is given next: a method `inc` that increments the field `x.f` by an arbitrary value `i`.

```viper,editable,playground
field f : Int

method inc(x: Ref, i: Int)
  requires acc(x.f)
  ensures true
{
  x.f := x.f + i
}
```

The program above declares a single integer (`Int`) field `f`, and the aforementioned increment method. The reference type (`Ref`) is built in; values of this type (other than the special value `null`) represent objects in Viper, which are the possible receivers for field accesses. Method `inc`'s *specification* (sometimes called its *contract*, in other languages) is expressed via its precondition (`requires`) and postcondition (`ensures`).

> **Exercise**
> * You can run the example by hitting the "play" button - it should verify  without errors.
> * Comment out the `requires` line (the method precondition) and re-run the example - this will result in a verification error, since permission to access `x.f` is no longer guaranteed to be held.
> * Implement an additional method that requires permission to `x.f` in its precondition and calls `inc(x, 0)` twice in its body. Does the current specification of `inc` suffice here? Can you guess what the problem is, and solve it?

In the remainder of this section we proceed as follows:
After a brief description of Viper's program state, we introduce the basic permission-related features employed by Viper. In particular, we discuss permission-related statements in the Viper language, as well as permission-related assertions, when such assertions are well-defined, and how they can be used to specify properties such as (non-)aliasing. Finally, we present a refined notion of permission supported by Viper: *fractional* permissions, which enable simultaneous access to the same heap location by multiple methods or (when modelling these in Viper) concurrent threads.
<!-- In the remainder of this section, we will introduce the basic permission-related features employed by Viper. We will refine the above definition of program state later in the tutorial as we introduce more features of the Viper language and resources other than field permissions (cf. the [section on predicates](./predicates.md) and [section on magic wands](./magic-wands.md)). -->

# Permissions {#permissions}

## Introduction

Reasoning about the heap of a Viper program is governed by *field permissions*, which specify the heap locations that an operation — a statement, an expression or an assertion — may access, i.e., read and/or modify. 
Heap locations can be accessed only if the corresponding permission is *held* by the currently verified method. The simplest form of field permission is the *exclusive* permission to a heap location `x.f`; it expresses that the current method may read and write to the location, whereas other methods or threads are not allowed to access it in any way.
Every Viper operation, i.e., every statement, expression, or assertion, has an implicit or explicit specification expressing which field permissions the operation requires, i.e., which locations it accesses. The part of the heap denoted this way is called the *footprint* of an operation.
Permissions enable preserving information about heap values in Viper: as long as the footprint of an expression is disjoint from the footprint of a method call, it can be concluded that the call does not change the expression's value, even if the concrete method implementation is unknown. 
Preserving properties this way is called *framing*: e.g., the value of an expression is *framed* across a method call, or in general, across a statement.
For example: the footprints of the expression `x.f == 0` and the field assignment statement `x.f := 1` are not disjoint, and the property `x.f == 0` can therefore not be framed across the assignment. In contrast, the property could be framed across `y.f := 0` if `y` and `x` were known to not be aliases. Permissions can also be used to guarantee non-aliasing, as will be discussed in more detail [later](#non-aliasing).

In pre- and postconditions, and generally in assertions, permission to a field is denoted by an *accessibility predicate*: an assertion which is written `acc(x.f)`. An accessibility predicate in a method's precondition can be understood as an obligation for a caller to *transfer* the permission to the callee, thereby giving it up. Consequently, an accessibility predicate in a postcondition can be understood as a permission transfer in the opposite direction: from caller to callee.
 
A simple example is given next: a method `inc` that increments the field `x.f` by an arbitrary value `i`.

```silver {.runnable }
field f : Int

method inc(x: Ref, i: Int)
  requires acc(x.f)
  ensures true
{
  x.f := x.f + i
}
```

The program above declares a single integer (`Int`) field `f`, and the aforementioned increment method. The reference type (`Ref`) is built in; values of this type (other than `null`) represent objects in Viper, which are the possible receivers for field accesses. Method `inc`'s *specification* (sometimes called *contract*) is expressed via its precondition (`requires`) and postcondition (`ensures`).

//exercise//

* You can run the example by hitting the "play" button - it should verify  without errors.
* Comment out the `requires` line (the method precondition) - this will result in a verification error, since permission to access `x.f` is no longer guaranteed to be held.
* Implement an additional method that requires permission to `x.f` in its precondition and calls `inc(x, 0)` twice in its body. Does the current specification of `inc` suffice here? Can you guess what the problem is, and solve it?

///

In the remainder of this section we proceed as follows: 
After a brief description of Viper's program state, we introduce the basic permission-related features employed by Viper. In particular, we discuss permission-related statements in the Viper language, as well as permission-related assertions, when they are well-defined, and how they can be used to specify properties like aliasing. Finally, we present a different kind of permissions supported in Viper, the *fractional* permissions, which enable simultaneous access to the same heap location by multiple methods or threads.
<!-- In the remainder of this section, we will introduce the basic permission-related features employed by Viper. We will refine the above definition of program state later in the tutorial as we introduce more features of the Viper language and resources other than field permissions (cf. the [section on predicates](#predicates) and [section on magic wands](#magic-wands)). -->

## Viper's Program State

Permissions are a part of a Viper program's state, alongside the values of variables and heap locations. Fields are only the first of several kinds of *resource* that will be explained in this tutorial; access to each resource is governed by appropriate permissions.
Different permissions can be held at different points in a Viper program: e.g., after allocating new memory on the heap, we would typically also add the permission to access those locations. In the next subsection, we will see the primitive operations Viper provides for manipulating the permissions currently held.

More precisely, a program state in Viper consists of:

* The values of all variables in scope: these include local variables, method input parameters (which cannot be assigned to in Viper), and method return parameters (which can) of the current method execution. Verification in Viper is *method-modular*: each method implementation is verified in isolation and, thus, the program state does not contain an explicit call stack.
* The permissions to field locations held by the current method execution.
* The values of those field locations to which permissions are currently held. Other field locations cannot be accessed.

The initial state of each method execution contains arbitrary values (of the appropriate types) for all variables in scope, and no permissions to heap locations. Permissions can be obtained through a suitable precondition (as in the `inc` example above); preconditions can also constrain the values of parameters and heap locations. Field locations to which permission is newly obtained will also contain arbitrary values.

## Inhaling and Exhaling {#inhaling-and-exhaling}

As previously mentioned, accessibility predicates in a method's precondition, such as `acc(x.f)` in the precondition of `inc`, can be understood as specifying that permission to a field (here `x.f`) must be transferred from caller to callee.
The process of gaining permission (which happens in the callee), is called *inhaling* permissions; the opposite process of losing permission (in the caller) is called *exhaling*. Both operations thus update the amount of currently held permissions: from a caller's perspective, permissions required by a precondition are removed before the call and permissions guaranteed by a postcondition are gained after the call returns. From a callee's perspective, the opposite happens.

Similar permission transfers also happen at other points in a Viper program; most notably, when verifying loops: a loop invariant specifies the permissions transferred (1) from the enclosing context to the first loop iteration, (2) from one loop iteration to the next, and (3) from the last loop iteration back to the enclosing context. Inside a loop body, heap locations may only be accessed if the required permissions have been explicitly transferred from the surrounding context to the loop body via the loop invariant.

In addition to specifying which permissions to transfer, Viper assertions may also specify constraints on values, just like in traditional specification languages. For example, a precondition `acc(x.f) && x.f > 0` requires permission to location `x.f` and that its value is positive. Note that the occurrence of `x.f` inside `acc(x.f)` denotes the *location* (in compiler parlance, `x.f` as an lvalue); the meaning of an accessibility predicate is independent of the value of `x.f` as an expression (as used, e.g., in `x.f > 0`).

Consider now the call in the first line of method `client` in the example below: `set`'s precondition specifies that the permission to `a.f` is transferred from the caller to the callee, and that `i` must be greater than `a.f`. Thus, method `client` has to exhale the permission to `a.f` (which are inhaled by `inc`) and the caller has to prove that `a.f < i` (which it currently cannot). Conversely, the postcondition causes the permission to be transferred back to the caller when `inc` terminates, i.e., they are inhaled by method ``client`, and the caller gains the knowledge that `a.f == 5`.
Upon verifying method `inc`, the opposite happens: permission to `x.f` is inhaled before the method body is verified, alongside the fact that `x.f < i`. After the body has been verified, permission to `x.f` are exhaled and it is checked that `x.f`'s value is indeed `i`.

```silver {.runnable }
field f: Int

method client(a: Ref)
  requires acc(a.f)
{
  set(a, 5)
  a.f := 6
}

method set(x: Ref, i: Int)
  requires acc(x.f) && x.f < i
  ensures  acc(x.f) && x.f == i
{
  x.f := i
}
```

//exercise//

* Method `client` fails to verify: the precondition of the call `set(a, 5)` may not hold. Can you fix this (without modifying method `set`)?
* Afterwards, add the following call as the last statement to method `client`: `set(x, x.f)`. Verification will now fail again. Remedy the situation by slightly weakening method `set`'s precondition.
* Finally, comment out the postcondition of method `inc`. Verification will fail again because method `client` does not have permission for the assignment to `a.f`. In fact, when a method call terminates, all remaining permissions that are not transferred back to its caller (via its postcondition) are *leaked*, that is, lost forever.

///

Note that when encoding, e.g., a garbage-collected source language into Viper, the design choice that any excess permissions get leaked is convenient; it allows heap-based data to simply go out of scope and become unreachable. However, in the case of `set` in the example above, such leaking is presumably not the intention. Viper can also be used to check that certain permissions are *not* leaked; see the `perm` expression in the [section on expressions](#expressions-and-assertions) for more details.

## Inhale and Exhale Statements {#inhale-and-exhale}

To enable the encoding of programming language features that are not directly supported by Viper, such as forking and joining threads or acquiring and releasing locks, Viper allows one to explicitly exhale or inhale permissions via the statements `exhale A` and `inhale A`, where `A` is a Viper assertion such as method `set`'s precondition `acc(x.f) && i < x.f`. From a caller's perspective, `set`'s pre- and postcondition can be seen as syntactic sugar for appropriate exhale and inhale statements before and after a call to the method.

The informal semantics of `exhale A` is as follows:

1. *Assert* that all value constraints in `A` hold; if not, verification fails
1. *Assert* that all permissions denoted (via accessibility predicates) by `A` are currently held; if not, verification fails
1. *Remove* the permissions denoted by `A`

The informal semantics of `inhale A` is as follows:

1. *Gain* the permissions denoted by `A` to the program state
1. *Assume* that all value constraints in `A` hold

As an example, consider the following Viper program (ignoring, for the moment, the commented-out lines):

```silver {.runnable }
field f: Int

method set_inex(x: Ref, i: Int) {
  // x.f := i
  inhale acc(x.f)
  x.f := i
  // exhale acc(x.f
  // x.f := i
}
```

Unlike the previous example, this method has no pre- and postcondition (no `requires`/`ensures`). This means that we start verification of the method body in a state with no permissions. The statement `inhale acc(x.f) && x.f < i` causes the corresponding permission to be added to the state, allowing the assignment on the following line to verify.

//exercise//

* Uncomment the first line of the method body. This will cause a verification error (on that line) since we try to access the location `x.f` before inhaling the necessary permission.
* Alternatively, uncomment the last two lines of the method body. This will cause a verification error for the last line, since we exhale the permission `x.f` before accessing the heap location.
* Uncomment the exhale statement and duplicate it, i.e., attempt to exhale permission to `x.f` twice. What happens?

///

## Self-Framing Assertions {#self-framing-assertions}

In order to have a clearly defined semantics, Viper assertions must be *well-defined*: e.g., partial operations (such as division) must not be applied outside of their domains (such as `1/n` if `n` is potentially zero).
Ensuring well-definedness is particularly important when assertions are evaluated in different contexts since the assertion must have the same, clearly defined meaning in all contexts.
In Viper, method specifications and loop invariants are such assertions: preconditions (postconditions) are evaluated both at the beginning (end) of verifying the method body and before (after) each call to the method; loop invariants are evaluated before and after a loop, as well as at the beginning and end of the loop body.
Such assertions are therefore checked to be well-defined in all states they can possibly be evaluated in.

<!--TODO: Would it make sense to have, probably at the end of the tutorial, a list of all well-definedness checks?-->

As an example, the assertion 'n < i/j' not allowed because it is not well-defined in all possible states (namely, in a state where `j == 0`). On the other hand, the assertion 'j > 0 && n < i/j' is allowed, since the first conjunct is well-defined by itself, and ensures the well-definedness of the second conjunct. Similarly, if an assertion is conditional, like the right hand side of an implication, then it must be well-defined only if the condition is true. For example, the assertion `j != 0 ==> n < i/j` is allowed because the right hand side is always well-defined if the left hand side is true.

In a permission logic, well-definedness also requires that all heap
locations read by the assertion are accessible, i.e., that the corresponding permissions are held. As before, this must be the case for all possible states in which the assertion could be evaluated.
To ensure this property, Viper requires specification assertions to be *self-framing*: i.e., each such assertion must include permission to at least the locations it reads. As an example, `acc(x.f)` and `acc(x.f) && x.f > 0` are self-framing, whereas `x.f > 0` and `acc(x.f.g)` are not: in the latter two cases, the meaning of the assertions depend on the value of the field `x.f`, to which permission is not included.

For technical reasons, Viper checks well-definedness, and thus also self-framingness, from left to right. The assertion `acc(x.f) && 0 < x.f` is therefore accepted as self-framing, but `0 < x.f && acc(x.f)` is not. However, this restriction is typically not a problem in practice.

The assertions in explicit `inhale` and `exhale` statements need not be self-framing because they are evaluated in only one program state; Viper will simply check that the well-definedness conditions for their assertions (e.g., that sufficient permissions are held) are true in that program state.

## Exclusive Permissions, Non-Aliasing and Framing

Permissions to field locations as described so far are exclusive; it is not possible to hold permission to a location more than once. This built-in principle can indirectly guarantee non-aliasing between references: inhaling the assertions `acc(x.f)` and `acc(y.f)` implies `x != y` because otherwise, the *exclusive* permission to `acc(x.f)` would be held twice. This is demonstrated by the following program:

```silver {.runnable }
field f: Int

method exclusivity(x: Ref, y: Ref) {
  inhale acc(x.f)
  inhale acc(y.f)
  exhale x != y
}
```

//exercise//

* Comment one of the two inhale statements. Does the exhale statement still succeed?
* Add the third inhale statement `inhale x == y` anywhere before the exhale statement and change the latter to `exhale false`. This demonstrates that it is not possible to hold more than one exclusive permission to `x.f`.

///

In Viper, accessibility predicates can be conjoined via `&&`: the two statements `inhale acc(x.f); inhale acc(y.f)` (semicolons are required in Viper only if statements are on the same line) are equivalent to the single statement `inhale acc(x.f) && acc(y.f)`. In both cases, the obtained permissions imply that `x` and `y` cannot be aliases.
Intuitively, the statement `inhale acc(x.f) && acc(y.f)` can be understood as inhaling permission to `acc(x.f)`, and in *addition* to that, inhaling the permission to `acc(y.f)`, while preserving the invariant that permission to a particular location is exclusive. Technically, this conjunction between resource assertions is strongly related to the *separating conjunction* from [separation logic](https://link.springer.com/chapter/10.1007/3-540-44802-0_1); details can be found in [this paper](https://lmcs.episciences.org/802). 

<!--**TODO: maybe consider also a link to wikipedia (for separation logic and separating conjunction), as suggested in one of the feedback e-mails **.-->

<!--**TODO: We could add a note here that briefly states that a conjunction between non-resource assertions, or a resource and a non-resource assertion, is the usual boolean conjunction. However, my feeling is that such a note will be more confusing then helpful.** -->

We can now see how exclusive permissions enable framing and modular verification, as illustrated by the next example: there, method `client` is able to frame the property `b.f == 3` across the call to `inc(a, 3)` because holding permission to both `a.f` and `b.f` implies that `a` and `b` cannot be aliases, and because method `inc`'s specification state that `inc` only requires access to `a.f`.
On a slightly more operational level, one can also explain the fact that `b.f == 3` can be framed across as follows: at the beginning of the call, method `client` transfers permission to `a.f` to the callee, but retains permission to `b.f`, which effectively means that the callee cannot modify `b.f` since it lacks the necessary permission.

```silver {.runnable }
field f: Int

method inc(x: Ref, i: Int)
  requires acc(x.f)
  ensures  acc(x.f)
  ensures  x.f == old(x.f) + i
{
  x.f := x.f + i
}

method client(a: Ref, b: Ref) {
  inhale acc(a.f) && acc(b.f)

  a.f := 1
  b.f := 3

  inc(a, 3)

  assert b.f == 3
}
```

Note:

* The expression `old(x.f)` in method `inc`'s postcondition denotes the value that `x.f` had at the beginning of the method call. In general, an *old expression* `old(e)` causes all heap-dependent subexpressions of `e` (in particular, field accesses and calls to heap-dependent functions) to be evaluated in the initial state of the corresponding method call. Note that local variables are not heap-dependent and are thus not affected by `old`.
* Method specifications can contain multiple `requires` and `ensures` clauses; all `requires` assertions are conjoined, and likewise for `ensures`.

//exercise//

* Add the statement `assert a.f == 4` to the end of method `client`; it will verify. Comment the second postcondition of `inc` to make it fail. What happens if you comment the first (but not the second) postcondition?
* Add a method `copyAndInc(x: Ref, y: Ref)` with the implementation `x.f := y.f + 1`. Can you give it a specification such that, when invoked as `copyAndInc(a, b)` by method `client` in place of the call `inc(a, 3)`, the statement `assert b.f == 3 && a.f == 4` in method `client` verifies?
* In method `client`, change the invocation of method `copyAndInc` to `copyAndInc(a, a)`, and change the `assert` statement to `assert b.f == 3 && a.f == 2`. You'll probably have to change the specifications of method `copyAndInc` to verify the new code.

///

## Fractional Permissions, Aliasing and Sharing {#non-aliasing}

Exclusive permissions are too restrictive for some applications. For instance, it is typically safe for multiple threads of a source program to concurrently access the same heap location as long as all accesses are reads. That is, read access can safely be shared. However, if any thread potentially writes to a heap location, no other should typically be allowed to concurrently read it (otherwise, the program has a *data race*). To support encoding such scenarios, Viper also supports *fractional permissions* with a *permission amount* between 0 and 1. Any non-zero permission amount allows read access to the corresponding heap location, but only the exclusive permission (1) allows modifications.

The general form of an accessibility predicate for field permissions is `acc(e.f, p)`, where `e` is a `Ref`-typed expression, `f` is a field name, and `p` denotes a permission amount. Permission amounts are denoted by `write` for exclusive permissions, `none` for zero permission, quotients of two `Int`-typed expressions `i1/i2` to denote a fractional permission, or a `Perm`-typed variable. `Perm` is the type of permission amounts, which is a built-in type that can be used like any other type. The permission amount `p` is optional and defaults to `write`. For example, `acc(e.f)`, `acc(e.f, write)` and `acc(e.f, 1/1)` all have the same meaning.

The next example illustrates the usage of fractional permissions to distinguish between read and write access: there, method `copyAndInc` requires write permission to `x.f`, but only read permission (we arbitrarily chose `1/2`, but any non-zero fraction will suffice) to `y.f`.

```silver {.runnable }
field f: Int

method copyAndInc(x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f, 1/2)
  ensures  acc(x.f) && acc(y.f, 1/2)
{
  x.f := y.f + 1
}
```

//exercise//

* Change the permission amount for `x.f` to `9/10`, i.e., the corresponding accessibility predicates to `acc(x.f, 9/10)`. Where does the code fail (and why)?
* Alternatively, change the implementation to `y.f := x.f + 1`.
* Revert to the original example. Afterwards, change the permission amount for `y.f` to `none` (or `0/1`). Where does the code fail (and why)?

///

Fractional permissions to the same location are *summed up*: inhaling `acc(x.f, p1) && acc(x.f, p2)` is equivalent to inhaling `acc(x.f, p1 + p2)`, and analogous for exhaling. As before, inhaling permissions maintains the invariant that write permission to a location are exclusive. With fractional permission in mind, this can be rephrased as maintaining the invariant that the permission amount to a location cannot exceed 1.

To illustrate this, consider the next example (and its exercises): there, the `assert` statement fails because holding one third permission to each `x.f` and `y.f` does not imply that `x` and `y` cannot be aliases, since the sum of the individual permission amounts does not exceed 1.

```silver {.runnable }
field f: Int

method test(x: Ref, y: Ref) {
  inhale acc(x.f, 1/2) && acc(y.f, 1/2)
  assert x != y
}
```

//exercise//

* Change both permission amounts to `2/3`. The `assert` statement will now verify.
* Revert to the original example. Afterwards, replace the `assert` statement by `inhale x == y` and add the statement `exhale acc(x.f, 1/1)` to the end of method `test`. The code verifies, which illustrates that permission amounts are summed up.
* Revert to the original example. Afterwards, replace the `assert` statement by `exhale acc(x.f, 1/8) && acc(x.f, 1/8)`, and add the subsequent statement `exhale acc(x.f, 1/4)`. The code verifies, which illustrates that permission amounts can be split up.
* Revert to the original example. Afterwards, add a third argument `z: Ref` to the signature of method `test`, add the conjunct `acc(z.f, 1/2)` to the `inhale` statement and change the `assert` statement to `x != y || x != z`. This verifies , but neither disjunct on their own will. Why?

///

While fractional permissions no longer always guarantee non-aliasing between references, as demonstrated by the previous example, they still enable framing, e.g., across method calls: from a caller's perspective, holding on to a non-zero permission amount to a location `x.f` across a method call guarantees that the value of `x.f` cannot be affected by the call. That is, because the callee would need to obtain write permission, i.e., permission amount 1, which cannot happen as long as the caller retains its fraction.

The next example illustrates the use of fractional permissions for framing: there, method `client` can frame the property `b.f == 3` across the call to `copyAndInc` because `client` retains half the permission to `b.f` across the call. Note that the postcondition of `copyAndInc` does not explicitly state that the value of `y.f` remains unchanged.

```silver {.runnable }
field f: Int

method copyAndInc(x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f, 1/2)
  ensures  acc(x.f) && acc(y.f, 1/2)
  ensures  x.f == y.f + 1
{
  x.f := y.f + 1
}

method client(a: Ref, b: Ref) {
  inhale acc(a.f) && acc(b.f)

  a.f := 1
  b.f := 3

  copyAndInc(a, b)

  assert b.f == 3 && a.f == 4
}
```

//exercise//

* Add the statement `exhale acc(b.f, 1/2)` right before the invocation of `copyAndInc`. Since method `client` temporarily loses all permission to `b.f`, the property `b.f == 3` can no longer be framed across the call. Note that method `client` cannot deduce modularly (i.e., without considering the body of method `copyAndInc`) that `copyAndInc` does *not* modify `b.f`; the method body might inhale the other half permission (e.g., modelling the acquisition of a lock) and thus, be able to assign to `b.f`.
* Can you fix the new code by changing the specifications of method `copyAndInc`?
* Revert to the original example. Afterwards, modify method `client` as follows: change the invocation of method `copyAndInc` to `copyAndInc(a, a)`, and change the `assert` statement to `assert b.f == 3 && a.f == 2`. To verify the resulting code, you'll have to change the specifications of method `copyAndInc`.
* Can you find specifications for method `copyAndInc` that allow verifying both versions of method `client`: the original implementation (`copyAndInc(a, b); assert b.f == 3 && a.f == 4`) and the new one (`copyAndInc(a, a); assert b.f == 3 && a.f == 2`). That is, can you find specifications that work, regardless of whether or not the passed references are aliases?

///
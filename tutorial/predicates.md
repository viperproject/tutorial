# Predicates {#predicates}

So far, we have only discussed the specification of programs with a statically-finite number of field locations; our specifications must enumerate all relevant locations in order to express the necessary permissions. However, realistic programs manipulate data structures of unbounded size. Viper supports two main features for specifying unbounded data structures on the heap: *predicates* and [quantified permissions](#quantified-permissions).

Viper predicates are top level declarations, which give a name to a parameterised assertion; a predicate can have any number of parameters, and its body can be any self-framing Viper assertion using only these parameters as variable names. Predicate definitions can be recursive, allowing them to denote permission to and properties of recursive heap structures such as linked lists and trees. Viper predicates may also be declared with *no* body (in this case, the predicate is *abstract*), which can be useful for representing assertions whose definitions should be hidden for information hiding reasons, or in more advanced applications of Viper, for adding new kinds of resource assertion to the verification problem at hand.

Predicates are introduced in top-level declarations of the form

```silver
predicate P(...) { A }
```

or

```silver
predicate P(...)
```

where `P` is a globally-unique predicate name, followed by a possibly-empty list of parameters, and `A` is the predicate body, that is, an assertion that may include usages of `P` as well as `P`'s parameters. Viper checks that predicate bodies are [self-framing](#self-framing-assertions). Declarations of the second form (that is, without body) introduce abstract predicates.

A predicate *instance* is written `P(e1,...,en)`, and is a second kind of resource assertion in Viper: [as for field permissions](#permissions), predicate instances can be inhaled and exhaled (added to and removed from the program state), and the Viper program state includes how many instances of which predicates are currently held.

In Viper, a predicate instance is *not* directly equivalent to the corresponding instantiation of the predicate's body, but these two assertions can be explicitly *exchanged* for one another. The statement `unfold P(...)` exchanges a predicate instance for its body; `fold P(...)` performs the inverse operation. Abstract predicates cannot be folded or unfolded.

In the following example, the predicate `tuple` represents permission to the `left` and `right` fields of some tuple (note that `this` is *not* a keyword in Viper). The method requires permission to the fields `this.left` and `this.right`. Intuitively speaking, the `tuple` predicate required by the precondition contains permissions to the fields `this.left` and `this.right`. Holding the predicate is not enough to be allowed to access these fields; the corresponding permissions, however, can be obtained by unfolding the predicate. On the last line of the method's body, these permission are folded back into the `tuple` predicate that is given back to the caller.

```silver {.runnable }
field left: Int
field right: Int

predicate tuple(this: Ref) {
  acc(this.left) && acc(this.right)
}

method setTuple(this: Ref, l: Int, r: Int)
  requires tuple(this)
  ensures tuple(this)
{
  unfold tuple(this)
  this.left := l
  this.right := r
  fold tuple(this)
}
```

Viper supports assertions of the form `unfolding P(...) in A`, which temporarily unfolds the predicate instance `P(...)` for (only) the evaluation of the assertion `A`. It is useful in contexts where statements are not allowed such as within method specifications and other assertions. For instance, in the example above we could add a postcondition `unfolding tuple(this) in this.left == l && this.right == r` to express that the entries of the tuple are set to `l` and `r`, respectively.

An `unfold` operation exchanges a predicate instance for its body; roughly speaking, the predicate instance is exhaled, and its body inhaled. Such an operation causes a verification failure if the predicate instance is not held. A `fold` operation exchanges a predicate body for a predicate instance; roughly speaking, the body is exhaled, and the instance inhaled. In both cases, however, in contrast to a standard exhale operation, these exhales do not remove information about the locations whose permissions have been exhaled because these permissions are still held, but perhaps folded (or no longer folded) into a predicate.

//exercise//

* In the previous example code above, comment out the `unfold` statement on the first line of `setTuple`. What fails, and why? What if you instead *duplicate* this statement?
* Try the same with the `fold` statement on the last line of the method body. What fails now?
* Add the postcondition `unfolding tuple(this) in this.left == l && this.right == r` to the original specification. What happens if you remove the `unfolding tuple(this) in` part, and why?
* After the `fold tuple(this)` statement, add the following line `unfold tuple(this); assert this.left == l; fold tuple(this)`. Why does this assertion succeed? What if you `exhale` and then `inhale` the predicate instance before the `unfold` you have just added?

///

Formally, recursive predicate definitions are interpreted with respect to their least fixpoint interpretations; informally, this implies the built-in assumption that any given predicate instance has a finite (but potentially unbounded) number of predicate instances folded within it. Note that a predicate instance may represent a statically-unknown set of permissions. Holding a predicate instance in a Viper state can be thought of as indirectly holding all of these permissions (though unfolding the predicate will be necessary to make direct use of them).

Analogously to field permissions, it is possible for a program state to hold *fractions* of predicate instances (unlike for field permissions, these can also be permission amounts *larger* than 1): this is denoted by accessibility predicates of the shape `acc(P(...), p)`. The simple syntax `P(...)` has the same meaning as `acc(P(...))`, which in turn has the same meaning as `acc(P(...), write)`. Folding or unfolding a fraction of a predicate effectively multiplies all permission amounts used for resources in the predicate body by the corresponding fraction. In the example below, one half of a `tuple` predicate is given to the method. Unfolding this half of the predicate yields half a permission for each of the fields `this.left` and `this.right`; which are sufficient permissions to read the fields.

```silver
method addTuple(this: Ref) returns (sum: Int)
  requires acc(tuple(this), 1/2)
  ensures acc(tuple(this), 1/2)
{
  unfold acc(tuple(this), 1/2)
  sum := this.left + this.right
  fold acc(tuple(this), 1/2)
}
```

The next example is an extract from an encoding of a singly-linked list implementation. The predicate `list` represents permission to the `elem` and `next` fields of all nodes in a null-terminated list. The `append` method requires an instance of the `list` predicate for its `this` parameter and returns this predicate instance to its caller. The body unfolds the predicate in order to get access to the fields of `this` and folds it back before terminating.

The statement `n := new(elem, next)` models object creation: it assigns a fresh reference to `n` and inhales write permission to `n.elem` and `n.next`. Notice that `unfold list(this)` will exchange the predicate instance for its body, which includes the predicate instance `list(this.next)` if `this.next != null`. This is important to understand why (when the first branch of the if-condition is taken)  *two* fold statements are needed: one for `list(n)` and another for `list(this)`: since `this.next` (or `n`) is no longer `null`, folding `list(this)` depends on first folding `list(n)`.

```silver {.runnable }
field elem: Int
field next: Ref

predicate list(this: Ref) {
  acc(this.elem) && acc(this.next) &&
  (this.next != null ==> list(this.next))
}

method append(this: Ref, e: Int)
  requires list(this)
  ensures  list(this)
{
  unfold list(this)

  if (this.next == null) {
    var n: Ref

    n := new(elem, next)
    n.elem := e
    n.next := null
    this.next := n

    fold list(n)
  } else {
    append(this.next, e)
  }
  fold list(this)
}
```

//exercise//

* Remove the precondition of `append` and observe that verification fails because the predicate instance to be unfolded (on the first line of the method body) is not held.
* Change the predicate definition to require all list elements to be non-negative; change the definition of `append` to maintain this property.
* Write a method that creates a cyclic list and attempt to fold the list predicate. Why does this fail? Hint: consider what does the assertion `acc(n.elem) && acc(n.elem)` mean in the context of separating conjunction.

///

It is often useful to declare predicates with several arguments, such as the following list segment predicate, which is commonly used in separation logic. The predicate's first argument denotes the start of the list segment, the second argument its end (i.e., the node directly after the segment) and the third
argument, a value-typed mathematical sequence, represents the values stored in the segment.

```silver {.runnable }
field elem : Int
field next : Ref

predicate lseg(first: Ref, last: Ref, values: Seq[Int])
{
  first != last ==>
    acc(first.elem) && acc(first.next) &&
    0 < |values| &&
    first.elem == values[0] &&
    lseg(first.next, last, values[1..])
}

method removeFirst(first: Ref, last: Ref, values: Seq[Int])
  returns  (value: Int, second: Ref)
  requires lseg(first, last, values)
  requires first != last
  ensures  lseg(second, last, values[1..])
{
  unfold lseg(first, last, values)

  value := first.elem
  second := first.next
}
```

//exercise//

* Implement a `prepend` method that adds an element at the front of the list. You can use `Seq(x) ++ s` to concatenate a sequence `s` to a singleton sequence containing `x` (see the [section on sequences](#sequences) for details). Note that verifyng your method will most-likely depend on a sequence identity such as `(Seq(x) ++ s)[1..] == s`. Such identities are not always provided automatically by the current sequence support. In case your example doesn't verify, try adding the appropriate equality in an `assert` statement; this should tell the verifier to prove the equality first, and then use it.
* Write a client method which takes an lseg in its precondition, calls your prepend method to prepend `42` to the front, and then uses `removeFirst` to get this value back. Can you assert afterwards that the returned value is `42`? What if you extend the specification of `removeFirst`?

///

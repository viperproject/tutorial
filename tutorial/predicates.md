# Predicates {#predicates}

So far, we have only discussed the specification of programs with a statically-finite number of fields; our specifications must enumerate all relevant fields in order to express the necessary permissions. However, realistic programs manipulate data structures of unbounded size. Viper supports two main features for specifying unbounded data structures: *predicates* and [quantified permissions](#quantified-permissions).

Viper predicates are top level declarations, which give a name to a parameterised assertion; a predicate can have any number of parameters, and its body can be any self-framing Viper assertion using only these parameters as variable names. Predicate definitions can be recursive, allowing them to denote permission to and properties of recursive heap structures such as linked lists and trees. Viper predicates may also be declared with *no* body (in this case, the predicate is *abstract*), which can be useful for representing assertions whose definitions should be hidden for information hiding reasons, or in more advanced applications of Viper, for adding new kinds of resource assertion to the verification problem at hand. 

Predicates are introduced in top-level declarations of the form
```
predicate P(...) { A }
```
or
```
predicate P(...)
```
where `P` is a globally-unique predicate name, followed by a possibly-empty list of parameters, and `A` is the predicate body, that is, an assertion that may include usages of `P` as well as `P`'s parameters. Viper checks that predicate bodies are [self-framing](#self-framing-assertions). Declarations of the second form (that is, without body) introduce abstract predicates.

A predicate *instance* is written `P(e1,...,en)`, and is a second kind of resource assertion in Viper: [as for field permissions](#permissions), predicate instances can be inhaled and exhaled (added to and removed from the program state), and the Viper program state includes how many instances of which predicates are currently held.

In Viper, a predicate instance is *not* directly equivalent to the corresponding instantiation of the predicate's body, but these two assertions can be explicitly *exchanged* for one another. The statement `unfold P(...)` exchanges a predicate instance for its body; `fold P(...)` performs the inverse operation. The assertion `unfolding P(...) in A` temporarily unfolds the predicate `P`, evaluates assertions `A`, and then re-folds `P`. It is useful in contexts where statements are not allowed such as within method specifications and other assertions. Abstract predicates cannot be folded or unfolded.

An `unfold` operation exchanges a predicate instance for its body; roughly speaking, the predicate instance is exhaled, and its body inhaled. Such an operation causes a verification failure if the predicate instance is not held. A `fold` operation exchanges a predicate body for a predicate instance; roughly speaking, the body is exhaled, and the instance inhaled. In both cases, however, in contrast to a standard exhale operation, these exhales do not remove information about the locations whose permissions have been exhaled because these permissions are still held, but perhaps folded (or no longer folded) into a predicate.

Formally, recursive predicate definitions are interpreted with respect to their least fixpoint interpretations; informally, this implies the built-in assumption that any given predicate instance has a finite (but potentially unbounded) number of predicate instances folded within it.

Analogously to field permissions, it is possible for a program state to hold *fractions* of predicate instances (unlike for field permissions, these can also be permission amounts *larger* than 1): this is denoted by accessibility predicates of the shape `acc(P(...), p)`. The simple syntax `P(...)` has the same meaning as `acc(P(...))`, which in turn as the same meaning as `acc(P(...), write)`. Folding or unfolding a fraction of a predicate effectively multiplies all permission amounts used for resources in the predicate body by the corresponding fraction.

The next example is an extract from an encoding of a singly-linked list implementation. The predicate `list` represents permission to the `elem` and `next` fields of all nodes in a null-terminated list. The `append` method requires an instance of the `list` predicate for its `this` parameter and returns this predicate instance to its caller. (note that `this` is *not* a keyword in Viper). The body unfolds the predicate in order to get access to the fields of `this` and folds it back before terminating.

The statement `n := new(elem, next)` models object instantiation: it assigns a fresh reference to `n` and inhales write permission to `n.elem` and `n.next`. Notice that `unfold list(this)` will exhale the predicate instance and inhale the body which includes inhaling the predicate instance `list(this.next)` if `this.next != null`. This is important to understand why (when the first branch of the if-condition is taken)  *two* fold statements are needed: one for `list(n)` and another for `list(this)`: since `this.next` (or `n`) is no longer `null`, folding `list(this)` depends on folding `list(n)` before.

Note that a predicate instance may represent a statically-unknown set of permissions. Owning the predicate instance means owning all those permissions.

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
predicate lseg(first: Ref, last: Ref, values: Seq[Int])
{
  first != last ==>
    acc(first.elem) && acc(first.next) &&
    0 < |values| &&
    first.elem == values[0] &&
    first.next != null &&
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

* Implement a `prepend` method that adds an element at the front of the list. You can use `Seq(x) ++ s` to concatenate a sequence `s` to a singleton sequence containing `x` (see the [section on sequences](#sequences) for details).
* The current predicate definition does not allow null-terminated list segments; consequently, folding `lseg(s, null, Seq(1))`, where `s.elem == 1` and `s.next == null`, will fail. Change the predicate definition such that null-terminated list segments can be specified. Do you need to make any changes to the code, in addition?

///
<!-- 
  The previous section on magic wands has been moved to
  the file magic-wands.md.old
-->

# Magic Wands {#magic-wands}

_Note: this section introduces a somewhat advanced feature of the Viper language, which users who are just starting-out with Viper may wish to [skip over for the moment](#statements)._

When reasoning with unbounded data structures, it can often be useful to specify properties of *partial* versions of these data structures. For example, during an iterative traversal of a linked list, one typically needs a specification relating the prefix of the list already visited, to a view of the overall data structure. Directly specifying such prefixes (or more generally, instances of data structures with a "hole"), tends to lead to auxiliary predicate definitions (e.g. an `lseg` predicate for list *segments*), which in turn necessitate additional lemmas or ghost methods for converting between multiple views of the same structure.

Viper includes a powerful alternative mechanism, which is often useful for evading these problems: the magic wand connective. A magic wand assertion is written ```A --* B```, where ```A``` and ```B``` are Viper assertions. Like permissions to field locations and instances of predicates, magic wands are a type of *resource*, instances of which can be held in a Viper program state; these can be added and removed from the state via ```inhale``` and ```exhale``` operations, just as for other resources.

A magic wand instance ```A --* B``` abstractly represents a resource which, if *combined* with the resources represented by ```A```, can be *exchanged* for the resources represented by ```B```. For example, ```A``` could represent the permissions to the postfix of a linked-list (where we are now), and ```B``` could represent the permissions to the entire list; the magic wand then abstractly represents the leftover permissions to the prefix of the list. In this case, *both* the postfix ```A``` and a magic wand ```A --* B``` could be given up, to reobtain ```B```, describing the entire list. This "giving up" step, is called *applying* the magic wand, and is directed in Viper with an ```apply``` statement:

```silver
inhale A
inhale A --* B
apply A --* B
assert B // succeeds; would fail before the apply statement
```

To understand a typical use-case for magic wands more concretely, consider the following iterative code for appending two linked lists:

```silver
field next : Ref
field val : Int

method append_iterative(l1 : Ref, l2: Ref)
  {
    if(l1.next == null) { // easy case
      l1.next := l2
    } else {
      var tmp : Ref := l1.next

      while(tmp.next != null)
      {
        tmp := tmp.next
      }
      tmp.next := l2
    }
  }
```

Using a standard linked-list predicate `list`, and a function `elems` to fetch the sequence of elements stored in a linked-list, we can specify the intended behaviour of our method, and add a first-attempt at a loop invariant, as follows:

```silver {.runnable }
field next : Ref
field val : Int

predicate list(start : Ref)
{
  acc(start.val) && acc(start.next) &&
      (start.next != null ==> list(start.next))
}

function elems(start: Ref) : Seq[Int]
  requires list(start)
{
  unfolding list(start) in (
    (start.next == null ? Seq(start.val) :
     Seq(start.val) ++ elems(start.next) ))  
}

method append_iterative(l1 : Ref, l2: Ref)
  requires list(l1) && list(l2) && l2 != null
  ensures list(l1)
  ensures elems(l1) == old(elems(l1) ++ elems(l2))
  {
    unfold list(l1)
    if(l1.next == null) { // easy case
      l1.next := l2; fold list(l1)
    } else {
      var tmp : Ref := l1.next
      var index : Int := 1 // extra variable: useful for specification

      while(unfolding list(tmp) in tmp.next != null)
        invariant index >= 0
        invariant list(tmp)
        // what about the prefix of the list?
      {
        unfold list(tmp)
        var prev : Ref := tmp // extra variable: useful for specification
        tmp := tmp.next
        index := index + 1
      }
      unfold list(tmp)
      tmp.next := l2
      fold list(tmp)
      // how do we get back to list(l1) ?
    }
  }
```

In this version of the code, we've added the extra variables `index` (representing how far through the linked-list the `tmp` reference is), and `prev`; both will be convenient for writing a specification later in this section. As commented in the file, the specification is not sufficient to verify the code. The loop invariant tracks permission to the postfix linked-list (referenced by `tmp`). However, it includes neither permissions nor value information about the *prefix* of the list between `l1` and the `tmp` reference. Since these permissions are not tracked by the loop invariant, they are effectively leaked during the loop execution; with the loop invariant given there is no way after the loop to obtain permission to the entire list (the predicate instance `list(l1)`), as required in the postcondition.

//exercise//

* Run the example code above. The check of the postcondition should fail, since the required predicate instance `list(l1)` is not held after the loop.
* Try changing the loop invariant by adding the additional conjunct `&& elems(tmp) == old(elems(l1))[index..]` at the end. Re-run the example - the behaviour should be unchanged. This conjunct expresses that the elements from `tmp` onwards have not been modified so far.
* Instead of this additional conjunct, why can't we simply write `&& elems(tmp) == old(elems(tmp))`? You might like to try making this change, and running the example. Recall that `old` expressions do not affect the evaluation of local variables; the reason is not to do with `tmp`'s value directly. Consider instead the precondition of `elems`; which predicate instances were held in the pre-state of the method?

///

We can now employ magic wands to retain the lost permissions. In order to retain (during execution of the loop) the permissions to the previously-visited nodes in the list, we use a magic wand `list(tmp) --* list(l1)`. This magic wand represents sufficient resources to guarantee that *if* we give up a `list(tmp)` predicate along with this wand, we can obtain a `list(l1)` predicate; conceptually, it represents the permissions to the earlier segment of the list between `l1` and `tmp`.

```silver {.runnable }
field next : Ref
field val : Int

predicate list(start : Ref)
{
  acc(start.val) && acc(start.next) &&
    (start.next != null ==> list(start.next))
}

function elems(start: Ref) : Seq[Int]
  requires list(start)
{
  unfolding list(start) in (
    (start.next == null ? Seq(start.val) :
     Seq(start.val) ++ elems(start.next) ))  
}

method appendit_wand(l1 : Ref, l2: Ref)
  requires list(l1) && list(l2) && l2 != null
  ensures list(l1) // && elems(l1) == old(elems(l1) ++ elems(l2))
  {
    unfold list(l1)
    if(l1.next == null) { // easy case
      l1.next := l2; fold list(l1)
    } else {
      var tmp : Ref := l1.next
      var index : Int := 1

      // package the magic wand required in the loop invariant below
      package list(tmp) --* list(l1)
      { // show how to get from list(tmp) to list(l1):
        fold list(l1) // also requires acc(l1.val) && acc(l1.next)
      }

      while(unfolding list(tmp) in tmp.next != null)
        invariant index >= 0
        invariant list(tmp)// && elems(tmp) == old(elems(l1))[index..]
        invariant list(tmp) --* list(l1) // magic wand instance
      {
        unfold list(tmp)
        var prev : Ref := tmp
        tmp := tmp.next
        index := index + 1

        package list(tmp) --* list(l1) // package new magic wand
        { // we get from list(tmp) to list(l1) by ...
          fold list(prev)
          apply list(prev) --* list(l1)
        }  
      }
      unfold list(tmp)
      tmp.next := l2
      fold list(tmp)
      apply list(tmp) --* list(l1) // regain predicate for whole list
    }
  }
```

The additional loop invariant includes an instance of a magic wand: `list(tmp) --* list(l1)`. Such a magic wand instance denotes a new kind of *resource* in Viper (in addition to field permissions and predicate instances); as such, it can be inhaled and exhaled just as other resource assertions. This particular magic wand instance can (when applied), be used up to exchange *any* `list(tmp)` predicate instance for a `list(l1)` predicate instance. In this example, the magic wand notionally represents the permissions to the prefix of the list between `l1` and `tmp`. These magic wand instances are created via `package` operations, which are explained below.

//exercise//

* Run the example code above. The check of the postcondition should succeed, in contrast to the previous example.
* Try changing the loop invariant by adding the additional conjunct `&& elems(tmp) == old(elems(l1))[index..]` at the end. Re-run the example - the behaviour should be unchanged. This conjunct expresses that the elements from `tmp` onwards have not been modified so far.
* Instead of this additional conjunct, why can't we simply write `&& elems(tmp) == old(elems(tmp))`? You might like to try making this change, and running the example. Recall that `old` expressions do not affect the evaluation of local variables; the reason is not to do with `tmp`'s value directly. Consider instead the precondition of `elems`; which predicate instances were held in the pre-state of the method?

///

## Package operations

There are two ways in which a magic wand instance can be added to the resources held in the program state: they can be inhaled (just as any other Viper resource), or we can instruct Viper to construct a new magic wand instance with a `package` statement. As an example to explain the feature, we will consider the `package` before the loop in the code example above. A `package` statement consists of the keyword followed by the desired magic wand instance (in this case, `list(tmp) --* list(l1)`), along with an optional block of code delimited by braces. The role of a `package` statement is to create (and justify the creation of) a new magic wand instance in the following way:

* A subset of the resources held in the _current state_ must be identified as necessary for justifying the new magic wand instance. These must be sufficient resources to ensure that, given the additional resources described in the wand left-hand-side, those on the wand's right-hand-side can be produced. This set of resources is _taken_ from the current state, and is called the _footprint_ of the newly-created magic wand instance. In our example, these are the field permissions `acc(l1.val) && acc(l1.next)` (since, along with the wand's left-hand-side `list(tmp)`, these are sufficient to guarantee the wand's right-hand-side `list(l1)`).
* The `package` operation must check that, given the selected footprint of resources from the current state, in _any heap_ in which the wand's left-hand-side assertion is held, the combination of these resources can be exchanged for the wand right-hand-side. Any field locations framed by permissions in the wand's footprint will be assumed to be unchanged for this check (e.g. `l1.next == tmp` is known in our example, since permission to `l1.next` is in the wand's footprint). The check is made during the `package` operation by successively attempting to match the resources required on the right-hand-side with resources provided on the left; if not found on the left-hand-side, the resources must instead be found in the current state (or else the `package` operation fails with a verification error), and are taken for the wand's footprint. See our [ECOOP'15](http://pm.inf.ethz.ch/publications/getpdf.php?bibname=Own&id=SchwerhoffSummers15.pdf) paper for more details of how wand footprints are chosen.
* It is often the case that the combination of the wand's left-hand-side and footprint do not _directly_ yield the wand's right-hand-side, but instead can do so after a number of additional operations are performed. These operations can be specified in the block attached to the `package` statement. In our example, the wand left-hand-side `list(tmp)` combined with the wand footprint `acc(l1.val) && acc(l1.next)` are sufficient to guarantee `list(l1)` _after_ performing the operation `fold list(l1)`, which is given in the block.

//exercise//

* In the same version of the example above, add a statement `assert acc(l1.next)` just before the first `package` statement. Run the example; there should be no error. Now try moving your `assert` statement to _after_ the `package` operation (and its attached block). You should now get an assertion failure; the permission to `l1.next` has been used up in the wand's footprint.
* Try removing the `fold list(l1)` statement from the first `package` statement. What error do you now get, when running the example?

///

## Heap-dependent expressions

So far, we have used magic wands with only resource assertions on their left- and right-hand-sides. However, in order to prove functional properties about our programs, we will as usual need to employ heap-dependent expressions (e.g. field dereferences and function calls) in our specifications. For example, to prove the postcondition `elems(l1) == old(elems(l1) ++ elems(l2))` we need a magic wand which guarantees something about the elements of the lists in our program.

 Magic wands can include any Viper assertions and expressions, provided that the left- and right-hand-sides are self-framing assertions. Heap dependent expressions used inside magic wands do _not_ refer to the values in the current heap. Instead, a heap dependent expression on the left of a magic wand refers to the heap when the wand is applied; those on the right-hand-side refer to the heap resulting from the application of the wand.

Recall that the magic wand used so far is `list(tmp) --* list(l1)`. One way to finish our example is to express that the elements that `list(l1)` _will have_ after applying the magic wand are guaranteed to be a prefix of the elements from the original list, plus whichever elements `list(tmp)` has at the point of applying the magic wand. Informally, we might consider writing something like `elems(l1) == old(elems(l1)[..index]) ++ elems(tmp)`. However, this expression is not quite well-defined; we never hold _both_ the predicate `list(l1)` and the predicate `list(tmp)` at the same time; `list(tmp)` is given up as part of applying the magic wand itself. In order to evaluate heap-dependent expressions in the state corresponding to the wand's left-hand-side, Viper supports the construct: `old[lhs](e)`, which may only be used in the right-hand-side of a magic wand, and causes the expression `e` to be evaluated in the corresponding left-hand state. Thus, we can express our desired magic wand as: `list(tmp) --* list(l1) && elems(l1) == old(elems(l1)[..index]) ++ old[lhs](elems(tmp))`. The corresponding full version of the example above is presented below:

```silver {.runnable }
field next : Ref
field val : Int

predicate list(start : Ref)
{
  acc(start.val) && acc(start.next) &&
    (start.next != null ==> list(start.next))
}

function elems(start: Ref) : Seq[Int]
  requires list(start)
{
  unfolding list(start) in (
    (start.next == null ? Seq(start.val) :
     Seq(start.val) ++ elems(start.next) ))  
}

method appendit_wand(l1 : Ref, l2: Ref)
  requires list(l1) && list(l2) && l2 != null
  ensures list(l1) && elems(l1) == old(elems(l1) ++ elems(l2))
  {
    unfold list(l1)
    if(l1.next == null) {
      l1.next := l2
      fold list(l1)
    } else {
      var tmp : Ref := l1.next
      var index : Int := 1

      package list(tmp) --* list(l1) && elems(l1) == old(elems(l1)[..index]) ++ old[lhs](elems(tmp))
      {
        fold list(l1)
      }

      while(unfolding list(tmp) in tmp.next != null)
        invariant index >= 0
        invariant list(tmp) && elems(tmp) == old(elems(l1))[index..]
        invariant list(tmp) --* list(l1) && elems(l1) == old(elems(l1)[..index]) ++ old[lhs](elems(tmp))
      {
        unfold list(tmp)
        var prev : Ref := tmp
        tmp := tmp.next
        index := index + 1

        package list(tmp) --* list(l1) && elems(l1) == old(elems(l1)[..index]) ++ old[lhs](elems(tmp))
        {
          fold list(prev)
          apply list(prev) --* list(l1) && elems(l1) == old(elems(l1)[..index-1]) ++ old[lhs](elems(prev))
        }  
      }
      unfold list(tmp)
      tmp.next := l2
      fold list(tmp)
      apply list(tmp) --* list(l1) && elems(l1) == old(elems(l1)[..index]) ++ old[lhs](elems(tmp))
    }
  }
```

<!---

```silver {.runnable }

field next : Ref
field val : Int

predicate list(start : Ref)
{
  acc(start.val) && acc(start.next) &&
    (start.next != null ==> list(start.next))
}

function elems(start: Ref) : Seq[Int]
  requires list(start)
{
  unfolding list(start) in (
    (start.next == null ?
      Seq(start.val) :
      Seq(start.val) ++ elems(start.next)
    )
  )  
}

define Appended(sublist,prefix,suffix) list(sublist) && elems(sublist) == prefix ++ suffix

method appendit_wand(l1 : Ref, l2: Ref)
  requires list(l1) && list(l2) && l2 != null
  ensures list(l1) && elems(l1) == old(elems(l1) ++ elems(l2))
  {
    unfold list(l1)
    if(l1.next == null) {
      l1.next := l2
      fold list(l1)
    } else {
      var tmp : Ref := l1.next
      var index : Int := 1
      var tmpelems : Seq[Int] := elems(tmp)

      package Appended(tmp,tmpelems,old(elems(l2))) --*
        Appended(l1,old(elems(l1)),old(elems(l2)))
      {
        fold list(l1)
      }

      while(unfolding list(tmp) in tmp.next != null)
        invariant index >= 0
        invariant list(tmp) && elems(tmp) == old(elems(l1))[index..]
        invariant let tmpelemsnow == (elems(tmp)) in
          Appended(tmp,tmpelemsnow,old(elems(l2))) --*
          Appended(l1,old(elems(l1)),old(elems(l2)))
      {
        var prevelems : Seq[Int] := elems(tmp)
        unfold list(tmp)
        var prev : Ref := tmp
        tmp := tmp.next
        index := index + 1

        tmpelems := elems(tmp)

        package Appended(tmp,tmpelems,old(elems(l2))) --*
          Appended(l1,old(elems(l1)),old(elems(l2)))
        {
          fold list(prev)
          apply Appended(prev,prevelems,old(elems(l2))) --*
          Appended(l1,old(elems(l1)),old(elems(l2)))
        }  
      }
      tmpelems := elems(tmp)
      unfold list(tmp)
      tmp.next := l2
      fold list(tmp)
      apply Appended(tmp,tmpelems,old(elems(l2))) --*
          Appended(l1,old(elems(l1)),old(elems(l2)))
    }
  }
```

Preliminary references:

* Our [ECOOP'15](http://pm.inf.ethz.ch/publications/getpdf.php?bibname=Own&id=SchwerhoffSummers15.pdf) paper on Viper's support for magic wands
* Our [online repository of Viper examples](http://viper.ethz.ch/examples/) contains several examples that use magic wands

-->

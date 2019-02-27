<!-- 
  The previous section on magic wands has been moved to
  the file magic-wands.md.old
-->
# Magic Wands (section under construction) {#magic-wands}

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
Using a standard linked-list predicate `list`, and
a function `elems` to fetch the sequence of elements stored in a linked-list, we can specify the intended behaviour of our method, and add a first-attempt at a loop invariant, as follows:
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

In this version of the code, we've added the extra variables `index` (representing how far through the linked-list the `tmp` reference is), and `prev`; both will be convenient for writing a specification. As commented in the file, the specification is not sufficient to verify the code. The loop invariant tracks permission to the postfix linked-list (referenced by `tmp`). However, it includes neither permissions nor value information about the *prefix* of the list between `l1` and the `tmp` reference. Since these permissions are not tracked by the loop invariant, they are effectively leaked during the loop execution; with the loop invariant given there is no way after the loop to obtain permission to the entire list (the predicate instance `list(l1)`), as required in the postcondition.

//exercise//

* Run the example code above. The check of the postcondition should fail, since the required predicate instance `list(l1)` is not held after the loop.
* Try changing the loop invariant by adding the additional conjunct ` && elems(tmp) == old(elems(l1))[index..]` at the end. Re-run the example - the behaviour should be unchanged. This conjunct expresses that the elements from `tmp` onwards have not been modified so far.
* Instead of this additional conjunct, why can't we simply write ` && elems(tmp) == old(elems(tmp))`? You might like to try making this change, and running the example. Recall that `old` expressions do not affect the evaluation of local variables; the reason is not to do with `tmp`'s value directly. Consider instead the precondition of `elems`; which predicate instances were held in the pre-state of the method?

///

We can now employ magic wands to retain the lost permissions. In order to retain (during execution of the loop) the permissions to the previously-visited nodes in the list, we use a magic wand `list(tmp) --* list(l1)`. This magic wand represents sufficient resources to guarantee that *if* we give up a `list(tmp)` predicate along with this wand, we can obtain a `list(l1)` predicate; conceptually, it represents the permissions to the earlier segment of the list between `l1` and `tmp`.

--- to be written ---

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
        fold list(l1) 
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
                
        package list(tmp) --* list(l1) // obtain new magic wand
        { // we get from list(tmp) to list(l1) by ...
          fold list(prev)
          apply list(prev) --* list(l1)
        }  
      }
      unfold list(tmp)
      tmp.next := l2
      fold list(tmp)
      apply list(tmp) --* list(l1)
    }
  }
```


--- to be continued ---
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

<!--
Preliminary references:

* Our [ECOOP'15](http://pm.inf.ethz.ch/publications/getpdf.php?bibname=Own&id=SchwerhoffSummers15.pdf) paper on Viper's support for magic wands 
* Our [online repository of Viper examples](http://viper.ethz.ch/examples/)
contains several examples that use magic wands
-->
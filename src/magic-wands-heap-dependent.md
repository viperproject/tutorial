# Heap-dependent expressions

So far, we have used magic wands with only resource assertions on their left- and right-hand-sides. However, in order to prove functional properties about our programs, we will as usual need to employ heap-dependent expressions (e.g. field dereferences and function calls) in our specifications. For example, to prove the postcondition `elems(l1) == old(elems(l1) ++ elems(l2))` we need a magic wand which guarantees something about the elements of the lists in our program.

 Magic wands can include any Viper assertions and expressions, provided that the left- and right-hand-sides are self-framing assertions. Heap dependent expressions used inside magic wands do _not_ refer to the values in the current heap. Instead, a heap dependent expression on the left of a magic wand refers to the heap when the wand is applied; those on the right-hand-side refer to the heap resulting from the application of the wand.

Recall that the magic wand used so far is `list(tmp) --* list(l1)`. One way to finish our example is to express that the elements that `list(l1)` _will have_ after applying the magic wand are guaranteed to be a prefix of the elements from the original list, plus whichever elements `list(tmp)` has at the point of applying the magic wand. Informally, we might consider writing something like `elems(l1) == old(elems(l1)[..index]) ++ elems(tmp)`. However, this expression is not quite well-defined; we never hold _both_ the predicate `list(l1)` and the predicate `list(tmp)` at the same time; `list(tmp)` is given up as part of applying the magic wand itself. In order to evaluate heap-dependent expressions in the state corresponding to the wand's left-hand-side, Viper supports the construct: `old[lhs](e)`, which may only be used in the right-hand-side of a magic wand, and causes the expression `e` to be evaluated in the corresponding left-hand state. Thus, we can express our desired magic wand as: `list(tmp) --* list(l1) && elems(l1) == old(elems(l1)[..index]) ++ old[lhs](elems(tmp))`. The corresponding full version of the example above is presented below:

```viper,editable,playground
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

```viper,editable,playground

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

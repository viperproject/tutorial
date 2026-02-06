# Encoding an Array Datatype

We proceed next with an example encoding of integer arrays. Note that arrays are not built-in in Viper, so we have to model an array type. Since array locations should be on the heap, we do this with a combination of a domain, a [field](./language-top.md#fields), and [quantified permissions](./quantified-permissions.md). Let's first consider a suitable domain:

```viper,editable,playground
domain IArray {
  function slot(a: IArray, i: Int): Ref
  function len(a: IArray): Int
  function first(r: Ref): IArray
  function second(r: Ref): Int

  axiom all_diff {
    forall a: IArray, i: Int :: { slot(a,i) }
      first(slot(a,i)) == a && second(slot(a,i)) == i
  }

  axiom len_nonneg {
    forall a: IArray :: { len(a) }
      len(a) >= 0
  }
}
```

The idea behind this encoding is to use a Viper object with a single field to model each element of an array. The ```slot``` function plays the role of mapping an array and integer index to the corresponding object. We express that the ```slot``` function is an injective mapping via the axiom ```all_diff```. The two functions ```first``` and ```second``` together play the role of an inverse to the ```slot(a,i)``` function.
Intuitively, this axiom expresses that for any pair ```(a, i)```, ```slot(a,i)``` defines a unique object (which will provide the memory location for the array slot).

In addition, we encode the function ```len``` for specifying the length of an array, and the axiom ```len_nonneg``` which expresses that this function never returns a negative value.

Because the elements of the array will be located on the heap, we need a way of specifying permissions to a range of array elements. We can use quantified permissions for this, and create the following macro definition for specifying permissions to the whole array:

```viper
field val: Int
define access(a)
  (forall j: Int :: 0 <= j && j < len(a) ==> acc(slot(a,j).val))
```

Note that, in Viper, we cannot refer to a specific program state from within domains. In particular, we cannot mention `slot(a,j).val` inside the axioms of `IArray`, since its meaning depends on a particular heap, and its well-definedness condition depends on whether one holds the appropriate permissions. The state-dependent part of the array encoding is taken care of outside of this domain. In particular, we can now use ```access``` in the following client code:

```viper
method client()
{
  // Create an integer array with three elements
  var a: IArray
  inhale len(a) == 3
  inhale access(a) // access to all array slots

  // Initialize the elements of an array
  var i: Int := 0
  while ( i < len(a) )
    invariant 0 <= i && i <= len(a)
  {
    slot(a,i).val := -i // models a[i] := -i
    i := i + 1
  }
}
```

This method will not verify without adding a suitable loop invariant.
If we still try, Viper will report the following message:

```viper
Assignment might fail. There might be insufficient permission to access slot(a, i).val.
```

Therefore, we need to add the permissions to the array to the loop invariant:

```viper
    invariant access(a)
```

For a complete example, see the Viper encoding of [Array Max, by elimination](http://viper.ethz.ch/examples/max-array-elimination.html).

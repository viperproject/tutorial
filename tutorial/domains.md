# Domains {#domains}

Domains enable the definition of additional types, mathematical functions, and axioms that provide their properties. Syntactically, domains consist of a name (for the newly-introduced type), and a block in which a number of function declarations and axioms can be introduced. The following example shows a simple domain declaration:

```silver-runnable
domain MyDomain {
  function foo(): Int
  function bar(x: Bool): Bool

  axiom axFoo { foo() > 0 }
  axiom axBar { bar(true) }
  axiom axFoobar { bar(false) ==> foo() == 3 }
}
```

The functions declared in a domain are global: one can apply them in any other scope of the Viper program. Functions declared inside a domain are called *domain functions*; these are more restricted than the standard Viper functions described previously. In particular, domain functions cannot have preconditions; they can be applied in *any* state. They are also always abstract, i.e., cannot have a defined body. The typical way to attach any meaning to these otherwise-uninterpreted functions, is via domain axioms.

Domain axioms are also global: they define properties of the program which are assumed to hold *in all states*. Since there is no restriction on the states to which an axiom applies, it must be well-defined in all states; for this reason, domain axioms cannot refer to the values of heap locations, nor to permission amounts (e.g., via [perm expressions](#perm-expressions)). In practice, domain axioms are standard (often quantified) first-order logic assertions. Axiom names are used only for readability of the code, but are currently not optional.

//exercise//

```silver-runnable
domain Neg {
  function not(cond: Bool): Bool
}
method TestNeg() {
  
}
```

1. Consider the code snippet above.

2. Add an axiom `ax_Neg` expressing that the function ```not``` negates the condition ```cond```.

    i. Write the axiom using a universal quantifier.

    ii. Write the axiom without using quantifiers.

    Hint: Typically, domain axioms require quantifiers, as the domain (in the mathematical sense) of most domain functions is unbounded.

3. Fill in the body of method ```TestNeg``` with an assertion that tests the behavior of ```not```. (Hint: write an assertion that checks the following query for an arbitrary Boolean value `x`: `not(not(x)) == x`).

///

In the remainder of this section, we will illustrate some use-cases of domains for defining additional types and concepts within a Viper program.

## Declaring New Types

The following domain defines a new type ```MyType``` with two type parameters: 

```silver-runnable
domain MyType[A,B] {
  function constructor_a(x: A): MyType[A,B]
  function constructor_b(y: B): MyType[A,B]
  function bin_oper(a: MyType[A,B], b: MyType[A,B]): MyType[A,B]
}
```

In this demo we create a new type called ```MyType```. It's defined with two type parameters ```A``` and ```B```. The encoding provides two constructors and a binary operation.

The following client code demonstrates how the type ```MyType``` can be used in a Viper program:

```silver
method client(a: MyType[Bool, Ref])
  requires a == bin_oper(a,a)
{
  var b: MyType[Int, Bool] := constructor_a(11)
  var c: MyType[Int, Bool] := constructor_b(true)
  var d: MyType[Int, Bool] := bin_oper(b,c)
  
  // The following code will be rejected by the typechecker,
  //  because a and d are created with different type parameters.
  var e: MyType[Int, Bool] := bin_oper(a,d)
}
```

Note that Viper does not support type parameters as part of function and method declarations; the only type parameters available are those of the enclosing domain. This has the practical implication that one must instantiate all type parameters of a domain type before they can be used outside of the domain definition. This instantiation is usually implicit; so long as the type-checker can figure out the necessary instantiations, then they need not be provided.

By default, Viper provides only two built-in operations for domain types: ```==``` and ```!=```. Other operations must be encoded via domain functions and given a meaning via appropriate domain axioms. 

### Encoding a list ADT

For a more realistic demo, we can encode an algebraic list datatype. We start with the function declarations.

```silver-runnable
domain List[T] {
  /* Constructors */

  function Nil(): List[T]
  function Cons(head: T, tail: List[T]): List[T]

  /* Destructors */

  function head_Cons(xs: List[T]): T  // requires is_Cons(xs)
  function tail_Cons(xs: List[T]): List[T] // requires is_Cons(xs)

  /* Constructor types */

  function type(xs: List[T]): Int
  unique function type_Nil(): Int
  unique function type_Cons(): Int

  /* Axioms omitted */
}
```

A mathematical list needs two constructors: ```Nil```, which takes no parameters, and ```Cons```, which takes a scalar value of type ```T``` and the tail list (of type ```List[T]```) and returns the new list.

An algebraic datatype requires a deconstructor for each parameter of each of its constructors (alternatively, if one implements tuple types, one can write a single destructor for each constructor). In the case of a list ADT, we will need only two deconstructors (for the parameters of ```Cons```). The deconstructors are called ```head_Cons``` and ```tail_Cons```, respectively.

Finally, we encode the integer function ```type``` which denotes whether the type of the list constructor is ```Nil``` or ```Cons```. In this case, we could use a Boolean function for this purpose. However, there could be more than two constructors of an ADT in the general case.

Notice that we use the keyword ```unique``` to declare domain functions whose values (while not concretely known) should be guaranteed different from those returned by any other ```unique``` domain functions. Sometimes the value of a function is irrelevant by itself, as long as it is guaranteed to be unique, as in the case of identification functions ```type_Nil``` and ```type_Cons```.

The full axiomatisation of these functions and some use cases are available in the [Encoding ADTs example](http://viper.ethz.ch/examples/encoding-adts.html).

## Axiomatising Custom Theories

Custom axioms can specify the semantics of mathematical functions. Functions typically have parameters, hence the corresponding axioms usually have a universal quantification over a range of possible values as arguments.

```silver-runnable
domain MyInteger {
  function create_int(x: Int): MyInteger
  function get_value(a: MyInteger): Int
  function sum(a: MyInteger, b: MyInteger): MyInteger

  axiom axSum {
    forall a: MyInteger, b: MyInteger ::
      sum(a,b) == create_int( get_value(a) + get_value(b) )
  }
}
```

### Triggers

The axiom ```axSum``` uses a universal quantifier (```forall```) to express the value of ```sum(a,b)``` for arbitrary values of the arguments ```a``` and ```b```, respectively. In order to apply this axiom, the SMT-solver must instantiate the quantified variables with concrete values in a given context. So, as explained in the [section on quantifiers](#quantifiers), it is highly important to choose good triggers for the quantifier to avoid performance issues during the verification. Poorly selected triggers may as well disallow the instantiation of the quantifier in cases in which the instantiation is needed.

In the example above, one would intuitively expect the axiom ```axSum``` to be applied whenever the function ```sum``` is applied to some pair of arguments. Therefore, it makes sense to specify ```{ sum(a,b) }``` as the trigger, as in the example below:

```silver-runnable
domain MyInteger {
  function create_int(x: Int): MyInteger
  function get_value(a: MyInteger): Int
  function sum(a: MyInteger, b: MyInteger): MyInteger

  axiom axSum {
    forall a: MyInteger, b: MyInteger :: { sum(a,b) }
      sum(a,b) == create_int( get_value(a) + get_value(b) )
  }
}
```

Recall that a proper trigger must mention all quantified variables.

If the trigger is omitted, the Viper tools attempt to infer possible triggers based on the body of the quantifier. However, this can result in unreliable behavior in general; it is highly recommended to write triggers for all quantifiers in a Viper program. For example, if we remove the explicit trigger from the case above, any of the following triggering terms could be inferred:

* ```{ sum(a,b) }```
* ```{ get_value(a), get_value(b) }```
* ```{ sum(a,b) }{ get_value(a), get_value(b) }```
* ```{ get_value(a), get_value(b) }{ sum(a,b) }```

Recall that, for example, ```create_int( get_value(a) + get_value(b) )``` is not a valid trigger, because it contains the arithmetic operator `+`.

Sometimes it is beneficial to choose expressions as triggers which are _not_ present in the body of the quantifier. For instance, this can help avoiding [matching loops](http://www.hpl.hp.com/techreports/2003/HPL-2003-148.pdf).

### Axiom-Caused Unsoundness

Just as with any other kind of assumption in a Viper program, one can introduce unsoundness by adding domain axioms. For the simplest case, consider the following example: 

```silver-runnable
domain Foo {
  axiom Unsound {
    false
  }
}

method smokeTest()
{
  assert false // verifies
}
```

Viper is able to verify this program, because the axiom ```Unsound``` is assumed to be true in *all states* of the program, including those in the body of method ```test```. While unsoundnesses in user-defined axioms can be much more subtle than in this example, the simple strategy of checking that one cannot ```assert false``` at various program points is often effective for catching basic mistakes, especially if some other surprising verification result has already been observed.

//exercise//

```silver-runnable
domain MyInteger {
  // copied from above without modification

  function create_int(x: Int): MyInteger
  function get_value(a: MyInteger): Int
  function sum(a: MyInteger, b: MyInteger): MyInteger

  axiom axSum {
    forall a: MyInteger, b: MyInteger :: { sum(a,b) }
      sum(a,b) == create_int( get_value(a) + get_value(b) )
  }
}

method test1(a: MyInteger, b: MyInteger)
{
    assert get_value(a) + get_value(b) == get_value(sum(a, b))
}

method test2(i: Int, j:Int) 
{
    assert sum(create_int(i), create_int(j)) == create_int(i + j)
}
```

1. Consider the two test cases above for the previously-declared datatype `MyInteger`. Observe that these tests do not verify with just the one axiom `axSum`.

2. Write an additional axiom that fixes the problem.

    i. Try manually instantiating `axSum` for one of the tests.

    ii. What is the missing step in the reasoning that cannot be done without adding an additional axiom?

    Hint: One may view the `MyInteger` datatype as a simple ADT, which means that there exists a bijection between `Int` and `MyInteger`.

    iii. What is the right trigger for your axiom? Make sure that, together with your new axiom, `test1` and `test2` verify.

    iv. Add an `assert false` at the end of each of the methods, to check that your axiom has not introduced any clear unsoundness.

3. Can you think of any other axioms that can be added to the domain in order to define  `MyInteger` more completely? (Hint: does your axiom from the last step express a _bijection_ or an _injection_?)

///

## Encoding an Array Datatype {#array-domain}

We proceed next with an example encoding of integer arrays. Note that arrays are not built-in in Viper, so we have to model an array type. Since array locations should be on the heap, we do this with a combination of a domain, a [field](#top-level-declarations), and [quantified permissions](#quantified-permissions). Let's first consider a suitable domain:

```silver-runnable
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

```silver
field val: Int
define access(a)
  (forall j: Int :: 0 <= j && j < len(a) ==> acc(slot(a,j).val))
```

Note that, in Viper, we cannot refer to a specific program state from within domains. In particular, we cannot mention `slot(a,j).val` inside the axioms of `IArray`, since its meaning depends on a particular heap, and its well-definedness condition depends on whether one holds the appropriate permissions. The state-dependent part of the array encoding is taken care of outside of this domain. In particular, we can now use ```access``` in the following client code:

```silver
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
If we still try, Viper will reports the following message:

```silver
Assignment might fail. There might be insufficient permission to access slot(a, i).val.
```

Therefore, we need to add the permissions to the array to the loop invariant:

```silver
    invariant access(a)
```

For a complete example, see the Viper encoding of [Array Max, by elimination](http://viper.ethz.ch/examples/max-array-elimination.html).

## ADT plugin

```silver-runnable
adt List[T] {
    Nil()
    Cons(value: T, tail: List[T])
}
```

The ADT plugin is an extension to Viper that enables declarations of algebraic datatypes. These consist of one or more constructors, each of which has zero or more arguments. Any instance of such a datatype then corresponds to exactly one of these constructors. There is syntax to identify which constructor an instance corresponds to, as well as syntax to extract the arguments given to that constructor. As in the example above, ADTs can have type parameters and can be recursive.

Iternally, the ADT syntax is translated into domains and domain function applications.

The plugin is enabled by default, and can be disabled with the command-line option `--disableAdtPlugin`.

### Discriminators

For every constructor of the ADT, a *discriminator* is generated. Syntactically, this is a field with the name `is<Constructor>` with a `Bool` type.

```silver
assert Cons(1, Cons(2, Nil())).isCons
assert Nil().isNil
```

### Destructors

For every argument of every constructor of the ADT, a *destructor* is generated. This is a field that extracts the given argument out of the constructor, and is only well-defined if the ADT instance is known to correspond to the given constructor.

```silver
assert Cons(1, Nil()).value == 1
assert Cons(1, Nil()).tail == Nil()

// this expression is not well-defined:
// assert Nil().value == 0
```

### Derived methods

Similarly to derivable methods in Haskell or Rust, the ADT plugin provides a syntax to derive certain operations for ADTs.

```silver
import <adt/derives.vpr>

adt Name[...] {
    ...
} derives {
    ...
}
```

The block after the `derives` keyword is a list of functions that should be derived for the declared ADT. At the moment, the only supported operation is `contains`, but this may change in future Viper versions.

Note that the `import <adt/derives.vpr>` is required for derived methods to work.

### `contains`

When the `contains` operation is derived, the function `contains` becomes available for the given ADT. Given a value and an ADT instance, it evaluates to `true` if the former value is found inside the ADT instance, as one of its constructor arguments. This evaluation works recursively.

```silver-runnable
import <adt/derives.vpr>

adt List[T] {
    Nil()
    Cons(value: T, tail: List[T])
} derives {
    contains
}

method client() {
    var x: List[Int] := Cons(42, Cons(33, Nil()))

    // test for the "value" argument of type Int in x
    assert contains(42, x)
    assert contains(33, x)

    // test for the "tail" argument of type List[Int] in x
    assert contains((Nil() : List[Int]), x)
    assert contains(Cons(33, Nil()), x)
}
```

By default, all arguments of every constructor of an ADT are considered for the `contains` operation. An optional comma-separated blocklist of arguments can be declared, which will cause the `contains` operation to ignore the named arguments:

```silver-runnable
import <adt/derives.vpr>

adt Tree[T] {
    Leaf()
    Node(left: Tree[T], val: T, right: Tree[T])
} derives {
    contains without left, right
}

method client() {
    var x: Tree[Int] := Node(Leaf(), 42, Node(Leaf(), 33, Leaf()))
    assert contains(42, x)

    // will fail to prove, because "right" is in the blocklist
    assert contains(Node(Leaf(), 33, Leaf()), x)
}
````

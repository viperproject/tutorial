# Declaring New Types

The following domain defines a new type ```MyType``` with two type parameters: 

```viper,editable,playground
domain MyType[A,B] {
  function constructor_a(x: A): MyType[A,B]
  function constructor_b(y: B): MyType[A,B]
  function bin_oper(a: MyType[A,B], b: MyType[A,B]): MyType[A,B]
}
```

In this demo we create a new type called ```MyType```. It's defined with two type parameters ```A``` and ```B```. The encoding provides two constructors and a binary operation.

The following client code demonstrates how the type ```MyType``` can be used in a Viper program:

```viper
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

## Encoding a list ADT

For a more realistic demo, we can encode an algebraic list datatype. We start with the function declarations.

```viper,editable,playground
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

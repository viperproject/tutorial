# Domains {#domains}

Domains enable the definition of additional types, mathematical functions, and axioms that provide their properties. Syntactically, domains 
consist of a name (for the newly-introduced type), and a block in which a number of function declarations and axioms can be introduced. The following example shows a simple domain declaration: 

```silver {.runnable }
domain MyDomain {
  function foo(): Int
  function bar(x: Bool): Int

  axiom axFoo { foo() > 0 }
  axiom axBar { bar(true) }
  axiom axFoobar { bar(false) ==> foo() == 3 }
}
```

The functions declared in a domain are global: one can apply them in any other scope of the Viper program. Functions declared inside a domain are called *domain functions*; these are more restricted than the standard Viper functions described previously. In particular, domain functions cannot have preconditions; they can be applied in *any* state. They are also always abstract, i.e., cannot have a defined body. The typical way to attach any meaning to these otherwise-uninterpreted functions, is via domain axioms.

Domain axioms are also global: they define properties of the program which are assumed to hold *in all states*. Since there is no restriction on the states to which an axiom applies, it must be well-defined in all states; for this reason, domain axioms cannot refer to the values of heap locations, nor to permission amounts (e.g., via [`perm` expressions](#perm-expressions)). In practice, domain axioms are standard (often quantified) first-order logic assertions. Axiom names are used only for readability of the code, but are currently required. 

//exercise//

```silver {.runnable}
domain Neg {
  function not(cond: Bool): Bool
}
method TestNeg() {
  
}
```

1. Consider the code snippet above. 

2. Add an axiom `ax_Neg` s.t. that the function ```not``` negates the condition ```cond```. 

    i. Write the axiom using a universal quantifier. 

    ii. Write the axiom without using quantifiers. 

    Hint: Typically, domain axioms require quantifiers, as the domain (in the mathematical sense) of most functions is unbounded. 

3. Fill in the body of method ```TestNeg``` with an assertion that tests the behavior of ```not```. 

    Hint: Write an assertion that checks the following query for an arbitrary Boolean value `x`: `not(not(x)) == x`. 

///

In the remainder of this section, we will illustrate some use-cases of domains for defining additional types and concepts within a Viper program.

## Declaring New Types

The following domain defines a new type ```MyType``` with two type parameters: 

```silver {.runnable }
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

```silver {.runnable }
domain List[T] {
  /* Constructors */

  function Nil(): List[T]
  function Cons(head: T, tail: List[T]): List[T]

  /* Deconstructors */

  function head_Cons(xs: List[T]): T  // requires is_Cons(xs)
  function tail_Cons(xs: List[T]): List[T] // requires is_Cons(xs)

  /* Constructor types */

  function type(xs: List[T]): Int
  unique function type_Nil(): Int
  unique function type_Cons(): Int

  /* Axioms omitted */
}
```

A singly-linked list needs two constructors: ```Nil```, which takes no 
parameters, and ```Cons```, which takes a scalar value of type ```T``` 
and the tail list (of type ```List[T]```) and returns the new list. 

An algebraic datatype requires a deconstructor for each parameter of each of its constructors. In the case of a list ADT, we will need only two deconstructors (for the parameters of ```Cons```). The deconstructors are called ```head_Cons``` and ```tail_Cons```, respectively. 

Finally, we encode the integer function ```type``` which denotes whether the type of the list constructor is ```Nil``` or ```Cons```. In this case, we could use a Boolean function for this purpose. However, there could be more than two constructors of an ADT in the general case. 

Notice that we use the keyword ```unique``` for declaring functions which return a unique value. Sometimes the value of a function is irrelevant by itself, as long as it is guaranteed to be unique, as in the case of identification functions ```type_Nil``` and ```type_Cons```. 

The axiomatisation of these functions and some use cases are available in the [Encoding ADTs example](http://viper.ethz.ch/examples/encoding-adts.html). 



## Axiomatising Custom Theories

Custom axioms can specify the semantics of mathematical functions. Functions typically have parameters, hence the corresponding axioms usually have a universal quantification over a range of possible values as arguments. 

```silver {.runnable }
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

Quantifier instantiation is based on syntactic heuristics. The idea is that the axiom should be applied if a term matching a specified syntactic pattern, called the _trigger_, has been detected in the current context. In the example above, one would expect the axiom 
```axSum``` to be applied whenever the function ```sum``` is applied to some pair of arguments. Therefore, it makes sense to specify ```sum(a,b)``` as the trigger; this will have exactly the desired effect. Syntactically, triggers are specified by terms in ```{...}``` braces after the ```::``` in the quantifier, as in the example below:

```silver {.runnable }
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

Note that a proper trigger must mention all bounded (quantified) variables. 

If the trigger is omitted, the Viper tools attempt to infer possible triggers based on the body of the quantifier. However, this can result in unreliable behavior in general; it is highly recommended to write triggers for all quantifiers in a Viper program. 
For example, if we remove the explicit trigger from the case above, any of the following triggering terms could be inferred: 

* ```{ sum(a,b) }```
* ```{ get_value(a), get_value(b) }```
* ```{ sum(a,b) }{ get_value(a), get_value(b) }```
* ```{ get_value(a), get_value(b) }{ sum(a,b) }```

Note that multi-triggers (that have several independent terms, e.g., ```{ A(i), B(j) }```), may be treated by the SMT solver in an asymmentric fashion: Depending on certain internal parameters, the solver may choose to instantiate individual terms in a multi-trigger lazily or eagerly. It is guaranteed that the very first term has the highest priority. 

Note that, for example, ```create_int( get_value(a) + get_value(b) )``` is not a valid trigger, because it contains an expression with a ```+``` operator. 

Sometimes it is beneficial to choose triggers among patterns which are _not_ present in the body of the quantifier. For instance, this can help avoiding [matching loops](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml253.pdf). 


### Axiom-Caused Unsoundness

Just as with any other kind of assumption in a Viper program, one can introduce unsoundness by adding domain axioms. For the simplest case, consider the following example: 

```silver {.runnable }
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

Viper is able to verify this program, because the axiom ```Unsound``` influences all states of the program, including those in the body of method ```test```. While unsoundnesses in user-defined axioms can be much more subtle than in this example, the simple strategy of checking that one cannot ```assert false``` at various program points is often effective for catching basic mistakes, especially if some other surprising verification result had already been observed.

//exercise//

```silver {.runnable}
domain MyInteger { 
  //copied from above without modification

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

1. Consider the two test cases above for the priorly declared datatype `MyInteger`. Observe that these tests do not verify with just one axiom, `axSum`. 

2. Write an additional axiom that fixes the problem. 

    i. Try manually instantiating `axSum` for one of the tests. 

    ii. What is the missing step in the reasoning that cannot be done without adding an additional axiom? 

    Hint: One may view the `MyInteger` datatype as a simple ADT, which means that there exists a bijection between `Int` and `MyInteger`. 

    iii. What is the right trigger for your axiom? Make sure that, together with your new axiom, `test1` and `test2` verify. 

    iv. Implement a smoke test to check if your axiom has introduced unsoundness. 

    Hint: Try asserting `false` inside the test methods. 


3. Are there other axioms that can be added to the domain in order to define  `MyInteger` more completely? 

    Hint: Does your axiom from the last step express a _bijection_ or an _injection_? 

///

## Encoding an Array Datatype {#array-domain}

We proceed next with an example encoding of integer arrays. Note that arrays are not built-in in Viper, so we have to model an array type. Since array locations should be on the heap, we do this with a combination of a domain, a [field](#top-level-declarations), and [quantified permissions](#quantified-permissions). Let's first consider a suitable domain: 

```silver {.runnable }
domain IArray {
  function loc(a: IArray, i: Int): Ref
  function len(a: IArray): Int
  function first(r: Ref): IArray
  function second(r: Ref): Int

  axiom all_diff {
    forall a: IArray, i: Int :: { loc(a,i) }
      first(loc(a,i)) == a && second(loc(a,i)) == i
  }

  axiom len_nonneg {
    forall a: IArray :: { len(a) }
      len(a) >= 0
  }
}
```

The idea behind this encoding is to use a Viper object with a single field to model each element of the array. The ```loc``` function plays the role of mapping an array and integer index to the corresponding object. We express that the ```loc``` function is an injective mapping via the axiom ```all_diff```. The two functions ```first``` and 
```second``` together play the role of an inverse to the ```loc(a,i)``` function. 
Intuitively, this axiom expresses that for any pair ```(a, i)```, ```loc(a,i)``` defines a unique memory location. 

In addition, we encode the function ```len``` for specifying the length of an array, and the axiom ```len_nonneg``` which expresses that this function cannot be negative. 

Because the elements of the array will be located on the heap, we need a way of specifying permissions to a range of array elements. We can use quantified permissions for this, and create the following macro definition for specifying permissions to the whole array: 

```
field val: Int
define access(a) 
  (forall j: Int :: 0 <= j && j < len(a) ==> acc(loc(a,j).val))
```

Note that, in Viper, we _cannot read the program state from within domains_. In this case, we cannot mention `loc(a,j).val` inside the axioms of `IArray`, so the state-dependent part of the array encoding must be placed outside of this domain. 

Now we can use ```access``` in the following client code: 

```silver
method client() 
{
  // Create an integer array with three elements
  var a: IArray
  inhale len(a) == 3
  inhale access(a)

  // Initialize the elements of an array
  var i: Int := 0
  while ( i < len(a) ) 
    invariant 0 <= i && i <= len(a)
  {
    loc(a,i).val := -i
    i := i + 1
  }
}
```

This method will not verify without adding a suitable loop invariant. 
If we still try, Viper will reports the following message: 

```
Assignment might fail. There might be insufficient permission 
 to access loc(a, i).val.
```

Therefore, we need to add the permissions to the array to the loop 
invariant: 

```silver
    invariant access(a)
```

For a complete example, see the Viper encoding of 
[Array Max, by elimination](http://viper.ethz.ch/examples/max-array-elimination.html).Therefore, we need to add the permissions to the array to the loop 
invariant: 

```silver
    invariant access(a)
```

For a complete example, see the Viper encoding of 
[Array Max, by elimination](http://viper.ethz.ch/examples/max-array-elimination.html).
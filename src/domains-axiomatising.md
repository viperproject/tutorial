# Axiomatising Custom Theories

Custom axioms can specify the semantics of mathematical functions. Functions typically have parameters, hence the corresponding axioms usually have a universal quantification over a range of possible values as arguments.

```viper,editable,playground
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

## Triggers

The axiom ```axSum``` uses a universal quantifier (```forall```) to express the value of ```sum(a,b)``` for arbitrary values of the arguments ```a``` and ```b```, respectively. In order to apply this axiom, the SMT-solver must instantiate the quantified variables with concrete values in a given context. So, as explained in the [section on quantifiers](./quantifiers.md), it is highly important to choose good triggers for the quantifier to avoid performance issues during the verification. Poorly selected triggers may as well disallow the instantiation of the quantifier in cases in which the instantiation is needed.

In the example above, one would intuitively expect the axiom ```axSum``` to be applied whenever the function ```sum``` is applied to some pair of arguments. Therefore, it makes sense to specify ```{ sum(a,b) }``` as the trigger, as in the example below:

```viper,editable,playground
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

## Axiom-Caused Unsoundness

Just as with any other kind of assumption in a Viper program, one can introduce unsoundness by adding domain axioms. For the simplest case, consider the following example: 

```viper,editable,playground
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

```viper,editable,playground
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

> **Exercise**
> 1. Consider the two test cases above for the previously-declared datatype `MyInteger`. Observe that these tests do not verify with just the one axiom `axSum`.
> 2. Write an additional axiom that fixes the problem.
>    1. Try manually instantiating `axSum` for one of the tests.
>    2. What is the missing step in the reasoning that cannot be done without adding an additional axiom?
>
>       Hint: One may view the `MyInteger` datatype as a simple ADT, which means that there exists a bijection between `Int` and `MyInteger`.
>    3. What is the right trigger for your axiom? Make sure that, together with your new axiom, `test1` and `test2` verify.
>    4. Add an `assert false` at the end of each of the methods, to check that your axiom has not introduced any clear unsoundness.
> 3. Can you think of any other axioms that can be added to the domain in order to define  `MyInteger` more completely?
>
>    Hint: does your axiom from the last step express a _bijection_ or an _injection_?

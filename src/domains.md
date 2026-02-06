# Domains

Domains enable the definition of additional types, mathematical functions, and axioms that provide their properties. Syntactically, domains consist of a name (for the newly-introduced type), and a block in which a number of function declarations and axioms can be introduced. The following example shows a simple domain declaration:

```viper,editable,playground
domain MyDomain {
  function foo(): Int
  function bar(x: Bool): Bool

  axiom axFoo { foo() > 0 }
  axiom axBar { bar(true) }
  axiom axFoobar { bar(false) ==> foo() == 3 }
}
```

The functions declared in a domain are global: one can apply them in any other scope of the Viper program. Functions declared inside a domain are called *domain functions*; these are more restricted than the standard Viper functions described previously. In particular, domain functions cannot have preconditions; they can be applied in *any* state. They are also always abstract, i.e., cannot have a defined body. The typical way to attach any meaning to these otherwise-uninterpreted functions, is via domain axioms.

Domain axioms are also global: they define properties of the program which are assumed to hold *in all states*. Since there is no restriction on the states to which an axiom applies, it must be well-defined in all states; for this reason, domain axioms cannot refer to the values of heap locations, nor to permission amounts (e.g., via [perm expressions](./expressions-perm.md)). In practice, domain axioms are standard (often quantified) first-order logic assertions. Axiom names are used only for readability of the code, but are currently not optional.

```viper,editable,playground
domain Neg {
  function not(cond: Bool): Bool
}
method TestNeg() {
  
}
```

> **Exercise**
> 1. Consider the code snippet above.
> 2. Add an axiom `ax_Neg` expressing that the function ```not``` negates the condition ```cond```.
>    1. Write the axiom using a universal quantifier.
>    2. Write the axiom without using quantifiers.
>
>    Hint: Typically, domain axioms require quantifiers, as the domain (in the mathematical sense) of most domain functions is unbounded.
> 3. Fill in the body of method ```TestNeg``` with an assertion that tests the behavior of ```not```. (Hint: write an assertion that checks the following query for an arbitrary Boolean value `x`: `not(not(x)) == x`).

In the remainder of this section, we will illustrate some use-cases of domains for defining additional types and concepts within a Viper program.

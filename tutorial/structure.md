# Structure of Viper Programs
For a type safe Viper program to be correct, all methods and functions in it must be successfully verified against their specifications. The implementation of a Viper method consists of certain [imperative building blocks](#statements) (such as branch conditions, loops, etc.) whereas the specification consists of [assertions](#expressions-and-assertions) (contracts, loop invariants, etc.). Statements (or operations) may change the program state, whereas assertions cannot. In contrast, assertions can talk about properties of a particular state — so they can be used to specify the behavior of operations. What the implementation and the specification have in common is that they both make use of _expressions_. For all of these building blocks, Viper supports different means of abstraction. 

Methods can be viewed as a means of abstraction over operations. The caller of a method observes its behavior exclusively through the signature and the contracts. Viper methods are modular: For the caller, the method's implementation is invisible. Calling a method may result in modifications to the program state, therefore method calls cannot be used in specifications. On the one hand, the caller of a method must first satisfy the assertions in its precondition in order to obtain the assertions from its postcondition. On the other hand, in order to _verify_ the method, Viper must prove that the method's implementation adheres to the method's contracts. 

Functions can be viewed as a means of abstraction over (potentially state-dependent) expressions. Generally, the caller of a function observes three things. First, the precondition of the function is checked in the state in which the function is called. The precondition may include permission assertions that describe the _resources_ that the function may read from. Second, the function call is replaced by the expression in the function body (if present). Note that, unlike, methods, Viper functions are non-modular. Third, the postcondition is assumed. The postcondition of a function may not contain permission assertions: All permissions from the precondition are automatically returned after the function call. Refer to the [section on functions](#functions) for more details. 

Predicates can be viewed as a means of abstraction over assertions and resources. The body of a predicate is an assertion. Unlike functions, predicates are not automatically inlined: To replace a predicate with its body, one needs to manually unfold it. As a consequence, `unfold` is an operation that changes the program state, replacing the predicate resource with the resource specified by its body. The dual operation is called `fold`: Folding a predicate replaces the resource specified by its body with the predicate itself. Refer to the [section on predicates](#predicates) for more details. 

Bellow you can find a brief description and examples of the language constructs that can be used to write a Viper program.

## Top-level declarations

### Fields 

```silver
field val: Int
field next: Ref
```

* Declared by keyword `field`
* Every object has all fields (there are no classes in Viper)
* See the [permission section](#permissions) for examples

### Methods

```silver
method QSort(xs: Seq[Ref]) returns (ys: Seq[Ref])
  requires ... //precondition
  ensures ... //postcondition
{
  //body (optional)
}
```

* Declared by keyword `method`
* Have input and output parameters (e.g., `xs` and `ys`)
* Method calls can modify the program state; see the [section on statements](#statements) for details
    * Hence calls _cannot_ be used in specifications
* The modular verification principle
    * The body may include some number of _statements_ (including recursive calls)
    * The body is invisible at call sight (changing the body does not affect client code)
    * The precondition is checked before the method call
    * If a method has a body, Viper will attempt to verify the postcondition
    * The postcondition is assumed after the method call
* See the [permission section](#permissions) for examples

### Functions

```silver
function gte(x: Ref, a: Int): Int
  requires ... //precondition
  ensures ... //postcondition
{
  ...  //body (optional)
}
```

* Declared by keyword `function`
* Have input parameters (e.g., `x` and `a`) and one output return value
* The keyword `result` may be used in a function's postcondition to refer to the return value
* Function calls may read but not modify the program state
    * Hence calls _can_ be used in specifications
    * Hence permissions may be mentioned in the precondition, but not in the postcondition
* If a function has a body, the body includes a single _expression_ (possibly with recursive calls)
* Unlike methods, functions are non-modular: changing the body of a function affects clients code 
* See the [section on functions](#functions) for details

### Predicates

```silver
predicate list(head: Ref) {
  ... //body (optional)
}
```

* Declared by keyword `predicate`
* Have input parameters (e.g., `head`)
* Typically used to abstract over assertions and to specify the shape of recursive data structures
* See the [section on predicates](#predicates) for details

### Domains

```silver
domain Pair[A, B] {
  function getFirst(p: Pair[A, B]): A
  //other functions

  axiom ax_1 {
    ... //axiom body
  }
  //other axioms
}
```

* Declared by keyword `domain`
* Consist of uninterpreted functions and axioms
    * Domain function may have no body nor contracts
    * Domain axioms may not read the program state
* Useful for specifying custom mathematical theories
* See the [section on domains](#domains) for details

### Macros

```silver
define plus(a, b) (a+b)
define link(x, y) {
  assert x.next == null 
  x.next := y
}
```

* Declared by keyword `define`
* C-style, syntactically expanded macros
  * Hence macros are not type-checked
* Allow more-concise encodings
  * Macros without a body expand to _expressions_ (e.g., `plus`) or _assertions_
  * Macros with a body expand to a list of statements (e.g., `link`)
* See the [array domain encoding](#array-domain) for an example

## Built-in types

* `Ref` for references (to objects, except for the built-in `Ref` constant `null`)
* `Bool` for Boolean values
* `Int` for mathematical (unbounded) integers
* `Rational` for mathematical (unbounded) rationals
* `Perm` for permission amounts (see the [section on permissions](#permissions) for details
* `Seq[T]` for immutable sequences with element type `T`
* `Set[T]` for immutable sets with element type `T`
* `Multiset[T]` for immutable multisets with element type `T`
* Additional types can be defined via [domains](#domains)

## Imports

```silver
import "path/to/extras.vpr"
```

Imports provide a simple mechanism for splitting the program across several Viper source files. 

* A relative or absolute path to a Viper file may be used (according to the Java/ Unix style and in double quotes)
* `import` adds the imported program as a preamble to the current one
* Transitive imports are supported
* Each Viper file may only be imported once
* Recursive imports are resolved via depth-first traversal
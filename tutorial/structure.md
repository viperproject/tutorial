# Structure of Viper Programs
For a type safe Viper program to be correct, all methods and functions in it must be successfully verified against their specifications. The implementation of a Viper method consists of certain [imperative building blocks](#statements) (such as branch conditions, loops, etc.) whereas the specification consists of [assertions](#expressions-and-assertions) (contracts, loop invariants, etc.). Statements (or operations) may change the program state, whereas assertions cannot. In contrast, assertions can talk about properties of a particular state — so they can be used to specify the behavior of operations. What the implementation and the specification have in common is that they both make use of _expressions_. For all of these building blocks, Viper supports different means of abstraction. 

Methods can be viewed as a means of abstraction over a sequence of operations (i.e. the execution of a potentially-unbounded number of statements). The caller of a method observes its behavior exclusively through the method's signature and its specification (its preconditions and postconditions). Viper method calls are treated modularly: for the caller of a method, the method's implementation can be thought of as invisible. Calling a method may result in modifications to the program state, therefore method calls cannot be used in specifications. On the one hand, the caller of a method must first satisfy the assertions in its precondition in order to obtain the assertions from its postcondition. On the other hand, in order to _verify_ a method itself, Viper must prove that the method's implementation adheres to the method's specification.

Functions can be viewed as a means of abstraction over (potentially state-dependent) expressions. Generally, the caller of a function observes three things. First, the precondition of the function is checked in the state in which the function is called. The precondition may include assertions denoting _resources_, such as [permissions to field locations](#permissions) that the the function may read from. Second, the function application's result value is equated with the expression in the function's body (if provided); note that this usage of the function's implementation is a difference from the handling of methods. Third, the function's postconditions are assumed. The postcondition of a function may _not_ contain resource assertions (e.g. denoting field permissions): all resources from the precondition are automatically returned after the function application. Refer to the [section on functions](#functions) for more details.

Predicates can be viewed as a means of abstraction over assertions (including resources such as field permissions). The body of a predicate is an assertion. Unlike functions, predicates are not automatically inlined: to replace a predicate with its body, Viper provides an explicit `unfold` statement. An `unfold` is an operation that changes the program state, replacing the predicate resource with the assertions specified by its body. The dual operation is called a `fold`: folding a predicate replaces the resources specified by its body with an instance of the predicate itself. Refer to the [section on predicates](#predicates) for more details.

Below you can find a brief description and examples of the language constructs that can be used to write a Viper program. Note that the order in which top-level declarations are written is not important, as names are resolved against all declarations of the program (including later declarations).

# Language overview

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
  requires ... // precondition
  ensures ... // postcondition
{
  // body (optional)
}
```

* Declared by keyword `method`
* Have input and output parameters (e.g., `xs` and `ys`)
* Method calls can modify the program state; see the [section on statements](#statements) for details
  * Hence calls _cannot_ be used in specifications
* Modular verification of methods and method calls
  * The body may include some number of _statements_ (including recursive calls)
  * The body is invisible at call site (changing the body does not affect client code)
  * The precondition is checked before the method call (more precisely, it is [_exhaled_](#inhaling-and-exhaling))
  * The postcondition is assumed after the method call (more precisely, it is [_inhaled_](#inhaling-and-exhaling))
* See the [permission section](#permissions) for more details and examples

### Functions

```silver
function gte(x: Ref, a: Int): Int
  requires ... // precondition
  ensures ... // postcondition
{
  ...  // body (optional)
}
```

* Declared by keyword `function`
* Have input parameters (e.g., `x` and `a`) and one output return value
* The keyword `result` may be used in a function's postcondition to refer to the return value
* Function applications may read but not modify the program state
  * Function applications _can_ be used in specifications
  * Permissions (and resource assertions in general) may be mentioned in a function's precondition, but not in its postcondition
* If a function has a body, the body is a single _expression_ (possibly including recursive calls to functions)
* Unlike methods, function applications are not handled modularly (for functions with bodies): changing the body of a function affects client code
* See the [section on functions](#functions) for details

### Predicates

```silver
predicate list(this: Ref) {
  ... // body (optional)
}
```

* Declared by keyword `predicate`
* Have input parameters (e.g., `head`)
* Typically used to abstract over assertions and to specify the shape of recursive data structures
* Predicate instances (e.g. `list(x)`) are _resource assertions_ in Viper
* See the [section on predicates](#predicates) for details

### Domains

```silver
domain Pair[A, B] {
  function getFirst(p: Pair[A, B]): A
  // other functions

  axiom ax_1 {
    ... // axiom body
  }
  // other axioms
}
```

* Declared by keyword `domain`
* Have a name, which is introduced as an additional _type_ in the Viper program
* Domains may have type parameters (e.g. `A` and `B` above)
* A domain's body (delimited by braces) consists of a number function declarations, followed by a number of axioms
  * Domain functions (functions declared inside a `domain`) may have neither a body nor a specification; these are uninterpreted total mathematical functions
  * Domain axioms consist of name (following the `axiom` keyword), and a definition enclosed within braces (which is a boolean expression which may not read the program state in any way)
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
  * Macros are not type-checked until after expansion
  * However, macro bodies must be well-formed assertions / statements
* May have any number of (untyped) parameter names (e.g. `a` and `b` above)
* The are two kinds of macros
  * Macros defining assertions (or expressions) include the macro definition whitespace-separated afterwards (e.g. `plus` above)
  * Macros defining _statements_ include their definitions within braces (e.g. `link` above)
* See the [array domain encoding](#array-domain) for an example

## Built-in types

* `Ref` for references (to objects, except for the built-in `Ref` constant `null`)
* `Bool` for Boolean values
* `Int` for mathematical (unbounded) integers
* `Rational` for mathematical (unbounded) rationals
* `Perm` for permission amounts (see the [section on permissions](#permissions) for details)
* `Seq[T]` for immutable sequences with element type `T`
* `Set[T]` for immutable sets with element type `T`
* `Multiset[T]` for immutable multisets with element type `T`
* Additional types can be defined via [domains](#domains)

## Imports

```silver
import "path/to/extras.vpr"
```

Imports provide a simple mechanism for splitting a Viper program across several source files.

* A relative or absolute path to a Viper file may be used (according to the Java/Unix style and in double quotes)
* `import` adds the imported program as a preamble to the current one
* Transitive imports are supported and resolved via depth-first traversal of the import graph
* The depth-first traversal mechanism enforces that each Viper file is imported at most once,
  including in the cases of multiple (indirect) imports of the same file or of recursive imports.
# Top-level declarations

## Fields

```viper
field val: Int
field next: Ref
```

* Declared by keyword `field`
* Every object has all fields (there are no classes in Viper)
* See the [section on permissions](./permissions.md) for examples

## Methods

```viper
method QSort(xs: Seq[Ref]) returns (ys: Seq[Ref])
  requires ... // precondition
  ensures ... // postcondition
{
  // body (optional)
}
```

* Declared by keyword `method`
* Have input and output parameters (e.g., `xs` and `ys`)
* Method calls can modify the program state; see the [section on statements](./statements.md) for details
  * Hence calls _cannot_ be used in specifications
* Modular verification of methods and method calls
  * The body may include some number of _statements_ (including recursive calls)
  * The body is invisible at call site (changing the body does not affect client code)
  * The precondition is checked before the method call (more precisely, it is [_exhaled_](./permissions-inhale-exhale.md))
  * The postcondition is assumed after the method call (more precisely, it is [_inhaled_](./permissions-inhale-exhale.md))
* See the [section on permissions](./permissions.md) for more details and examples

## Functions {#intro-functions}

```viper
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
* See the [section on functions](./functions.md) for details

## Predicates {#intro-predicates}

```viper
predicate list(this: Ref) {
  ... // body (optional)
}
```

* Declared by keyword `predicate`
* Have input parameters (e.g., `head`)
* Typically used to abstract over assertions and to specify the shape of recursive data structures
* Predicate instances (e.g. `list(x)`) are _resource assertions_ in Viper
* See the [section on predicates](./predicates.md) for details

## Domains {#intro-domains}

```viper
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
* See the [section on domains](./domains.md) for details

## Macros

```viper
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
* See the [array domain encoding](./domains-array.md) for an example

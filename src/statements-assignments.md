# Assignments

Viper supports the following forms of assignments:

| Statement | Description |
| ---- | ---- |
| `x := e`  | Assignment to local variables or result parameters |
| `e1.f := e2` | Assignment to heap locations |
| `x, y := m(...)` | Method calls |
| `x := new(...)` | Object creation |

Assignments to local variables and result parameters of methods work as
expected. It is not possible to assign to input method parameters. Assignment to heap
locations requires the full permission to the heap location (here,
`e1.f`). Methods may have any number of result parameters; method call
statements use the appropriate number (and types) of variables on the left-hand side (using the same variable twice on the left-hand side is disallowed).
A
method call can be understood as an exhale of the method precondition, a reassignment of the variables used to store result parameters, and inhale of the method postcondition.
Finally, a `new` statement creates a new object and inhales exclusive permission
to all (possibly none) fields listed comma-separated within the parentheses. As a special case, `x := new(*)` inhales permission to
*all* fields declared in the Viper program. Note that neither method calls nor
object creation are expressions. Hence, they must not occur as receivers, method
arguments, etc.; instead of nesting these constructs, one typically assigns their results first to local variables, and then uses these.

Viper additionally supports some more flexible forms of declarations and assignments:

* Local variable declarations may declare several variables at once, e.g., `var a: Ref, b: Ref, c: Int`.
* Local variable declarations may include an initial assignment, e.g., `var x: Int := 5`; the right-hand side may also be a method call or object creation, e.g., `var y: Ref := new(*)`.
* Heap locations and newly-declared local variables may occur on the left-hand sides of method calls and object creations, e.g., `x.f := new(...)` and `a, x.f := m(...)`.

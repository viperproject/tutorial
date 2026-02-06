# Expressions

Viper supports a number of different kinds of expressions, which can be evaluated to a value of one of the types supported in Viper.

The primitive types supported in Viper are booleans (`Bool`), integers (`Int`), permission amounts (`Perm`), denoting real numbers, and references to heap objects (`Ref`). In addition, there are built-in parameterised set (`Set[T]`), multiset (`Multiset[T]`), sequence (`Seq[T]`), and map (`Map[T, U]`) types, and users can define custom types using [domains](./domains.md).

Evaluating an expression never changes the state of the program, i.e., expression evaluation has no side effects. However, expression evaluation comes with well-definedness conditions for some expressions: evaluating an expression can cause a verification failure if the expression is not well-defined in the current program state; this leads to a verification error. As an example, the expression `x % y` is not well-defined if `y` is equal to zero, and the expression `o.f` is only well-defined if the current method has the permission to read `o.f` (which also implies that `o` is not null).

In the following, we list the different kinds of expressions, remark on their well-definedness conditions (if any) and the value that they evaluate to.






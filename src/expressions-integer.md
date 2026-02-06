# Integer expressions

* constants, e.g. `-2`, `1023123909`. Integers in Viper are signed and unbounded.

* unary minus `-e`: Negates the value of `e` if `e` is itself an integer.

* addition, subtraction, multiplication, division, modulo (`e1 + e2`, `e1 - e2`, `e1 * e2`, `e1 / e2`, `e1 % e2`). For all of these, both operands are expected to be integers, and the result will be an integer. These operators are overloaded; similar operators exist returning `Perm`-typed values; Viper will choose the appropriate operator based on the type information available. The only observable ambiguity is for division, since integer division truncates and `Perm`-typed division does not. In ambiguous cases, the alternative syntax `e1 \ e2` can be used to force `Int`-typed division (`Perm`-typed is otherwise the default).

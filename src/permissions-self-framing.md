# Self-Framing Assertions

Some Viper expressions and assertions come with conditions under which they are *well-defined*: e.g., partial operations (such as division) must not be applied outside of their domains (such as `1/n` if `n` is potentially zero).
Well-definedness conditions in Viper guarantee not only that assertions have a meaningful semantics, but that this semantics will be consistent across multiple contexts in which specifications are evaluated. Examples are Viper method specifications and loop invariants: preconditions (postconditions) are evaluated both at the beginning (end) of verifying the method body and before (after) each call to the method; loop invariants are evaluated before and after a loop, as well as at the beginning and end of the loop body.
Such assertions are therefore checked to be guaranteed well-defined in all states they can possibly be evaluated in.

<!--TODO: Would it make sense to have, probably at the end of the tutorial, a list of all well-definedness checks?-->

As an example, the assertion `n < i/j` is not well-defined in general; it cannot be used in e.g. a method precondition unless that precondition also guarantees that the value of `j` cannot be `0`. The assertion `j > 0 && n < i/j` is well-defined, since the first conjunct is well-defined by itself, and ensures the well-definedness of the second conjunct. In general, the (short-circuiting) order of evaluation of logical connectives is taken into account for well-definedness conditions. For example, `j != 0 ==> n < i/j` is also well-defined (the right hand side's value is only used when the left hand side is true, which guarantees its well-definedness condition).

Well-definedness in Viper also requires that all heap locations read by the assertion are accessible, i.e., that the corresponding permissions are held. Again, this must be the case for all possible states in which the assertion could be evaluated.
To ensure this property, Viper requires specification assertions to be *self-framing*: i.e., each such assertion must include permission to at least the locations it reads. As an example, `acc(x.f)` and `acc(x.f) && x.f > 0` are self-framing, whereas `x.f > 0` and `acc(x.f.g)` are not: in the latter two cases, the meanings of the assertions depend on the value of the field `x.f`, to which permission is not included.

Viper checks well-definedness, and thus also self-framedness, according to a left-to-right evaluation order. The assertion `acc(x.f) && 0 < x.f` is therefore accepted as self-framing, but `0 < x.f && acc(x.f)` is not. This restriction is typically easy to work around in practice.

The assertions in explicit `inhale` and `exhale` statements need not be self-framing because they are evaluated in only one program state; Viper will simply check that the well-definedness conditions for their assertions (e.g., that sufficient permissions are held) are true in that program state.

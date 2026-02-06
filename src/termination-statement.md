# Statement Termination (Experimental)

> **Warning**
>
> Termination checks outside of functions -- for methods and loops, and method and function calls -- are considered experimental: their semantics could change in the future, or they might be removed from Viper completely.
>
> We encourage you to experiment with the current implementation, and to let us know if it suits your needs and whether changes or additional features would benefit your verification efforts, etc.

## Function Calls inside Methods {#term_fct_calls}

The development of the *experimental* termination checks for statements was (partly) guided by Viper's intended use as an intermediate verification language. This shaped, among other things, how function calls are currently handled.

Front-ends may use Viper functions to encode (pure) program procedures, but front-ends may also use functions to encode proof-relevant properties. Similarly, Viper methods may be used to encode (impure) program procedures, or to encode proof lemmas. Moreover, encoded program procedures could contain Viper statements corresponding to actual statements from the source program, interspersed with Viper statements that encode additional proof steps.

Consider, e.g., a Viper function `elems(ll)` that denotes the set of all elements in a potentially cyclic linked-list `ll`. A statement such as `inhale es == elems(ll)` could be part of a sequence of program statements -- in which case `elems(ll)` should probably terminate -- or it could be an additional proof step, in which case it would suffice if `elems(ll)` were well-defined.

**Function calls inside Viper methods (as opposed to calls inside functions) are therefore (currently) not checked for termination**, and front-ends would have to generate appropriate checks where necessary. Potential alternatives include (1) to always check termination -- probably too restrictive; (2) to enable users to specify termination requirements at call-site, e.g. via attributes/annotations -- but the latter are currently not available in Viper.

## Checking Loop Termination {#term_loops}

Viper `while` loops accept decreases clauses at the position of invariants, as illustrated by the following code snippet:

```viper
while (0 < i)
  decreases i
{
  i := i - 1
}
```

Given such a specification, Viper will check that the termination measure decreases if the loop body is executed again. **A successful verification then implies that the loop is always bounded, i.e. that a finite unrolling of the loop exists**. Consequently, Viper does (currently) not check that each statement, including nested loops, in the loop body terminates, as illustrated by the next code snippet:

```viper
method m() // might not terminate

while (0 < i)
  decreases i // verifies successfully (finite unrolling exists)
{
  i := i - 1
  m()
  while (true) {}
}
```

We have chosen this approach for the following reasons (but are happy to receive feedback and discuss alternatives):

* Minimality: Interpreting loop termination as "a finite unrolling exists" can be seen as the weakest reasonable requirement, compared to the stronger (additional) requirement of all body statements having to terminate (note: the same argument does not apply to functions).

* Uniformity: When proving method termination (discussed next), the current approach directly exhibits the same behaviour for both syntactic `while` loops and loops encoded via `goto`s and `label`s (but see the note below). If loop bodies had to terminate as well, it would pose the question of which statements belonged to a goto-loop, which in general cannot be answered unambiguously (e.g. when inferring a while-loop from a goto-loop). This uniformity also extends to manually unrolled loops, as some front-ends might do.

* Expressiveness: If loop body termination checks are required, they can be encoded easily (potentially via a synthetic method that only hosts the loop body). 

* Familiarity: The same approach is used in Dafny (but then again, Dafny was not designed as an intermediate verification language)

## Checking Method Termination {#term_methods}

The currently implemented approach to checking termination of methods is similar to the previously described approach for functions: decreases clauses can be specified at the position of preconditions; if provided, **Viper checks that the termination measure decreases in each directly or indirectly recursive method invocation, and that other method calls, as well as loops, terminate**. As [previously described](#term_fct_calls), *function* applications inside methods are *not* checked for termination.

A straightforward example is method `sum`, shown next:

```viper,editable,playground
import <decreases/int.vpr>

method sum(n: Int) returns (res: Int)
  requires 0 <= n
  decreases
  ensures res == n * (n + 1) / 2
{
  res := 0
  var i: Int := 0;

  while (i <= n)
    invariant i <= (n + 1)
    invariant res == (i - 1) * i / 2
    decreases n-i
  {
    res := res + i
    i := i + 1
  }
}
```

> **Exercise**
> * Remove the decreases-clause from the loop and observe that the method no longer verifies.
> * Revert to the initial program, add declaration `method m()` to the program, and call `m` inside the loop. Observe that it is (again) the method that fails to verify now.
> * Avoid the error by removing the decreases-clause from method `sum` (or by adding a wildcard decreases-clause to method `m`).
> * Revert to the initial program, add a nested loop, e.g. `var j: Int := n; while(0 < j) { j := j - 1 }`, and observe the resulting verification failure. Experiment a bit with adding new and removing existing decreases clauses.

Final remark: Viper (currently) performs a call-graph analysis for methods to detect mutually recursive methods. Analogous to [the case of functions](./termination-special-tuples.md#term_empty_tuple), this is done for convenience, to unburden users from having to write "artificial" constant termination measures for non-recursive methods. This could be considered a deviation from Viper's otherwise method-modular verification approach -- please let us know if this poses a problem in your use case of Viper.

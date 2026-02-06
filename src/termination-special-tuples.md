# Special `decreases` Tuples

Viper supports three decreases tuples whose semantics require further explanation.

## Empty {#term_empty_tuple}

Consider the following pair of functions, where `compute` performs the actual computation and `facade` merely provides a default argument to `compute`:

```viper
function facade(i: Int): Int { compute(i, 0) }

function compute(i: Int, j: Int): Int { i + j }
```

Both functions have no decreases clause, and Viper thus won't generate termination checks. This may be fine now, since the functions obviously terminate, but if `compute` were changed to be recursive, potential non-termination might go unnoticed. To account for future code changes, users could use "artificial" constants as termination measures, but Viper offers a better solution: to ensure termination checks, users can specify empty tuples, and Viper's call-graph analysis (performed to detect [mutual recursion](./termination-mutual-recursion.md)) effectively infers suitable constants.

```viper,editable,playground
function facade(i: Int): Int
  decreases
{ compute(i, 0) }

function compute(i: Int, j: Int): Int
  decreases
{ i + j }
```

> **Exercise**
> * Make the body of `compute` recursive, e.g., by changing it to `i <= 0 ? j : compute(i - 1, j + i)`, and verify the program
> * Provide a termination measure, so that the changed program verifies again

## Wildcard

Specifying a termination measure might not always be an option: it could be too cumbersome to express; it could be considered a problem to deal with later; or it could be that the function does not terminate in an operational sense, but is nevertheless well-defined. Simply omitting the decreases clause, however, might not be an option, e.g. because the function is called from another function, for which termination checks are generated.

For such cases, Viper offers the *wildcard* measure `_`, which expresses that a function is to be considered terminating, although no termination checks are generated. I.e., a wildcard measure is effectively an unchecked assumption.

```viper,editable,playground
function collatz(n: Int): Int
  requires 1 <= n
  decreases _ // I can't be bothered right now
{
  n == 1     ? n :
  n % 2 == 0 ? collatz(n / 2) :
               collatz(3 * n + 1)
}
```

## Star

To explicate that a function is not checked for termination, and may thus not terminate, Viper supports the *star* measure `*`. This special measure is equivalent to providing no decreases clause at all, but may be useful for documentation purposes.

```viper,editable,playground
function nonterm(): Int
  decreases * // Whole clause could as well have been omitted
{ 1 + nonterm() }
```

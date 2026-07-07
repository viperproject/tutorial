# Annotations

Viper declarations, statements and expressions may be prefixed with *annotations* of the form

```viper
@key("value1", "value2")
```

An annotation consists of a key and a possibly-empty list of string values, and attaches extra information to the annotated program element. Any number of annotations may be written on the same element. Annotations do not change the meaning of a program: keys that are unknown to Viper are simply ignored (which allows, e.g., front-ends to attach their own tool-specific metadata to Viper programs), and the annotations known to Viper only influence *how* a program is verified, not what it means.

## Opaque functions

By default, the body of a [function](./functions.md) is available to the verifier at every application of the function. For functions with complex bodies, this can be a performance problem (the SMT solver has to consider many facts that may be irrelevant to the proof at hand), and it can also be at odds with information hiding. Annotating a function with `@opaque()` hides its body: at applications of the function, the verifier only uses its specification, as if the function were [abstract](./functions.md). The function's body is still verified against its specification as usual.

To make the definition of an opaque function available at a *specific* application, that application can be prefixed with the `@reveal()` annotation. Revealing an application does not recursively reveal further applications: in the example below, revealing `fac(3)` makes the fact `fac(3) == 3 * fac(2)` available, but the value of `fac(2)` remains hidden until that application is revealed as well.

```viper,editable,playground
@opaque()
function fac(i: Int): Int
{
  i <= 1 ? 1 : i * fac(i - 1)
}

method opaqueClient()
{
  var x: Int := fac(3)
  // The definition of fac is hidden, so the following assertion
  // fails, even though it is true.
  assert x == 6
}

method revealClient()
{
  var x: Int := @reveal() fac(3)
  assert x == 3 * fac(2)
  assert x == 3 * @reveal() fac(2)
  assert x == 3 * 2 * @reveal() fac(1)
  assert x == 6
}
```

> **Exercise**
> * Remove the `@opaque()` annotation (and the `@reveal()` annotations). Both methods now verify.
> * Restore the annotations. Then remove only the `@reveal()` on `fac(1)` in `revealClient`. Which assertions fail, and why?

## Backend-specific annotations

The remaining annotations known to Viper are hints to a specific verification backend; backends that do not understand them ignore them. In particular, Viper's Symbolic Execution (SE) backend supports several annotations that mirror its command-line options, but apply to a single method only, including:

* `@exhaleMode("n")` on a method: overrides the exhale mode used to verify this method (corresponding to the `--exhaleMode` command-line option).
* `@moreJoins("n")` on a method: joins verification paths after branches instead of exploring them separately (corresponding to `--moreJoins`), which can speed up verification of methods with many branches.
* `@stateConsolidationMode("n")` on a method: selects the state consolidation mode used for this method (corresponding to `--stateConsolidationMode`).
* `@proverConfigArgs("key=value")` on a method: passes additional configuration options to the SMT solver while verifying this method (corresponding to `--proverConfigArgs`).
* `@weight("n")` on a quantifier: sets the weight of the quantifier in the SMT encoding, which influences how eagerly the SMT solver instantiates it (higher weights mean fewer instantiations).

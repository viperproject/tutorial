# Quantifiers

Viper's assertions can include `forall` and `exists` quantifiers, with the following syntax:

```viper
forall [vars] :: [triggers] A
```

```viper
exists [vars] :: e
```

Here `[vars]` is a list of comma-separated declarations of variables which are being quantified over, `[triggers]` consists of a number of so-called *trigger expressions* in curly braces (explained next), and `A` (and `e`) is a Viper assertion (respectively, boolean expression) potentially including the quantified variables. Unlike existential quantifiers, `forall` quantifiers in Viper *may* contain resource assertions; this possibility is explained in the [section on quantified permissions](./quantified-permissions.md).

Trigger expressions take a crucial role in guiding the SMT solver towards a quick solution, by restricting the instantiations of a quantified assertion. In particular, when a `forall`-quantified assertion is a hypothesis for a proof goal, the triggers inform the SMT solver to instantiate the quantifier only when it encounters expressions (which are not themselves under a quantifier) of forms matching the trigger. Let's first illustrate with an example:

```viper
assume forall i: Int, j: Int :: {f(i), g(j)} f(i) && i < j ==> g(j)
assert ...f(h(5))...g(k(7))... // some proof goal
```

Here, assuming that the SMT solver encounters both the expressions `f(h(5))` and `g(k(7))`, the body of the quantification will be instantiated with `i == h(5)` and `j == k(7)`, obtaining `f(h(5)) && h(5) < k(7) ==> g(k(7))`. If no other pairs of expressions matching the triggers are encountered, no other instantiations of the quantifier will be made.

In general, a `forall` quantifier can have any number of sets of trigger expressions; these are written one after the other, each enclosed within braces. Multiple such sets prescribe alternative triggering conditions; multiple expressions *within* a single trigger set prescribe that expressions matching *each* of the trigger expressions must be encountered before an instantiation may be made.

You can check how triggers affect the verification in the following examples:

- in `restrictive_triggers` the triggers are too restrictive and do not allow the right instantiation of the quantifier;
- in `dangerous_triggers` the bad choice of the triggers leads to an infinite loop of instantiations (in this case, each instantiation results in a new expression which matches the trigger): a problem known as [*matching loop*](http://www.hpl.hp.com/techreports/2003/HPL-2003-148.pdf). In this case, the SMT solver times out without providing an answer.
- in `good_triggers` the choice of the triggers allows the SMT solver to quickly provide the right answer, preventing the problematic matching loop of the previous example.

```viper,editable,playground
function magic(i:Int) : Int

method restrictive_triggers()
{
  // Our definition of `magic`, with a very restrictive trigger
  assume forall i: Int :: { magic(magic(magic(i))) }
    magic(magic(i)) == magic(2 * i) + i

  // The following should verify. However, the verification fails
  // because the triggers are too restrictive and the quantifier
  // can not be intantiated.
  assert magic(magic(10)) == magic(20) + 10
}

method dangerous_triggers()
{
  // Our definition of `magic`, with a matching loop
  assume forall i: Int :: { magic(i) }
    magic(magic(i)) == magic(2 * i) + i

  // The following should fail, because our definition says nothing
  // about this equality. However, if you uncomment the assertion
  // the verification will time out and give no answer because of the
  // matching loop caused by instantiating the quantifier.
  // assert magic(magic(10)) == magic(87987978) + 10
}

method good_triggers()
{
  // Our definition of `magic`
  assume forall i: Int :: { magic(magic(i)) }
    magic(magic(i)) == magic(2 * i) + i
  
  // The following verifies, as expected
  assert magic(magic(10)) == magic(20) + 10

  // The following fails, as expected, because our definition says
  // nothing about this equality. The verification terminates
  // quickly because we don't have matching loops; the SMT solver
  // quickly exhausts the available quantifier instantiations. 
  assert magic(magic(10)) == magic(87987978) + 10
}
```

There are a number of restrictions on what can be used as a set of trigger expressions:

  1. Each quantified variable must occur at least once in a trigger set.
  2. Each trigger expression must include at least one quantified variable.
  3. Each trigger expression must have some additional structure (typically a function application); a quantified variable alone cannot be used as a trigger expression.
  4. Arithmetic and boolean operators may *not* occur in trigger expressions.
  5. Accessibility predicates (the `acc` keyword) may not be used in trigger expressions.

Applications of both domain and top-level Viper functions can be used in trigger expressions, as can field dereference expressions (e.g. `x.f`) and Viper's built-in sequence and set operators. Note that the *types* of trigger expressions are not restricted; in particular, there is no requirement that trigger expressions are boolean-typed.

If no triggers are specified, Viper will infer them automatically with a heuristics based on the body of the quantifier. In some unfortunate cases this automatic choice will not be good enough and can lead to either incompletenesses (necessary instantiations which are not made) or matching loops; it is recommended to always specify triggers on Viper quantifiers.

The underlying tools currently have limited support for existential quantifications: the syntax for `exists` does not allow the specification of triggers (which play a dual role for existential quantifiers, in controlling the potential witnesses/instantiations considered when *proving* an existentially-quantified formula), so existential quantifications should be used sparingly due to the risk of matching loops. This limitation is planned to be lifted in the near future.

For more details on triggers and the e-matching approach to quantifier instantiation, we recommend the [Programming with Triggers](https://dl.acm.org/citation.cfm?id=1670416) paper.

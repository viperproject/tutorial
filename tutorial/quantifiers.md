# Quantifiers {#quantifiers}

Viper's assertions can include `forall` and `exists` quantifiers, with the following syntax:
```
forall [vars] :: [triggers] [e]
```
```
exists [vars] :: [e]
```

Here `[vars]` is a list of comma-separated declarations of variables which are being quantified over, `[triggers]` consists in a number of so called *trigger* expressions in curly braces, and `[e]` is a boolean expression using the quantified variables.

Trigger expressions take a crucial role in guiding the SMT solver towards a quick solution, by restricting the cases in which the quantification can be applied. That is, triggers inform the SMT solver to instantiate the quantifier only when it encounters an expression of the form of the trigger. Let us take an example:

```silver
forall i: Int, j: Int :: {f(i), g(j)} f(i) && i < j ==> g(j)
```

Here, assuming that the SMT solver encounters both the expressions `f(h(5))` and `g(k(7))`, the body of the quantification can be instantiated with `i == h(5)` and `j == k(7)`, obtaining `f(h(5)) && h(5) < k(7) ==> g(k(7))`.

You can check how triggers affect the verification in the following examples:

- in `restrictive_triggers` the triggers are too restrictive and do not allow the right instantiation of the quantifier;
- in `dangerous_triggers` the bad choice of the triggers leads to an infinite loop of instantiations, a problem known as [*matching loop*](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml253.pdf), thus the SMT solver times out without providing any good answer;
- in `good_triggers` the choice of the triggers allows the SMT solver to quickly provide the right answer, preventing the problematic matching loop of the previous example.

```silver {.runnable}
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
  // the verification times out and give no answer because of the
  // matching loop in the definition of the quantifier.
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
  // quickly because we don't have matching loops.
  assert magic(magic(10)) != magic(87987978) + 10
}
```

Not all expressions can be triggers: arithmetic operations, for example, are not allowed. Moreover, trigger expressions must always mention all variables being quantified over. It is also possible to specify multiple triggers by using multiple blocks in curly braces; the quantifier will then be triggered if the SMT solvers sees all expressions in any of the blocks.

If no triggers are specified, Viper will infer then automatically with an heuristic based on the body of the quantifier. In some unfortunate cases this automatic choice is not good enough and leads to a matching loop, so it is recommended to always specify the triggers, especially if the verification fails or takes too long.

The underling tools currently have limited support for existential quantifications: the syntax for `exists` does not allow to specify triggers, so existential quantifications should be used sparingly due to the risk of matching loops.

For more details on triggers, you can read the ["Programming with triggers"](https://dl.acm.org/citation.cfm?id=1670416) paper.
# Introduction

[Viper](http://viper.ethz.ch/) is a verification infrastructure that simplifies the development of program verifiers and facilitates rapid prototyping of verification techniques and tools. In contrast to similar infrastructures such as [Boogie](http://research.microsoft.com/en-us/projects/boogie/) and [Why3](http://why3.lri.fr/), Viper has strong support for permission logics such as separation logic and implicit dynamic frames. It supports permissions natively and uses them to express ownership of heap locations, which is useful to reason about heap-manipulating programs and thread interactions in concurrent software.

<img src="https://www.ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/images/Research/viper_architecture.png" alt="The Viper verification infrastructure" style="width: 100%;"/>

The Viper infrastructure, shown above, provides an intermediate language as well as two verification back-ends, one based on symbolic execution and one based on verification condition generation. Both back-ends ultimately use the SMT solver
[Z3](https://github.com/Z3Prover/z3) to discharge proof obligations. Front-end tools translate different source languages and verification
approaches into the Viper language and thereby benefit from its tool support and automation.

The Viper intermediate language is a simple sequential, object-based, imperative programming language. Even though it has been designed as an intermediate language, the Viper language supports both high-level features that are convenient to express verification problems manually as well as powerful low-level features that are useful to encode source languages and verification techniques automatically.

The following simple example shows a method that computes the sum of the first `n` positive natural numbers. The method declaration includes a *precondition* (the assertion following `requires`) to restrict the argument to non-negative values. This expresses the fact that method `sum` can only be assumed to behave correctly (in particular, do not crash) for non-negative values. The method declaration also includes a *postcondition* (the assertion following `ensures`) to guarantee properties of the result variable `res`. The postcondition is the only information that a caller of the method `sum` can use to correlate the call result and argument. In particular, in absence of post-condition a caller of method `sum` cannot make use of the fact that the result is non-negative. This would be required, for example, in order to be able to call `sum` on its own result. Method preconditions and postconditions together make up a method's *specification*.

 Viper verifies *partial correctness* of program statements; that is, verification guarantees that *if* a program state is reached, then the properties specified at that program state are guaranteed to hold. For example, the postcondition of `sum` is guaranteed to hold whenever a call to `sum` terminates. Verification of loops also requires specification: the loop in `sum`'s body needs a *loop invariant* (if omitted, the default loop invariant is `true`, which is typically not strong enough to prove interesting properties of the program). The loop invariant in `sum` could also be written in one line with the boolean operator `&&` placed between the two assertions.

```silver {.runnable }
method sum(n: Int) returns (res: Int)
  requires 0 <= n
  ensures  res == n * (n + 1) / 2
{
  res := 0
  var i: Int := 0;
  while(i <= n)
    invariant i <= (n + 1)
    invariant res == (i - 1) * i / 2
  {
    res := res + i
    i := i + 1
  }
}
```


//exercise//

* This tutorial features runnable examples, which use the Viper verifiers. You can run the example by hitting the "play" button - it should verify without errors.
* You can also edit the examples freely, and try out your own versions. Try commenting the `requires` line (the method *precondition*) - this
  should result in a verification error. Viper supports both `//` and `/* ... */` styles for comments.
* Try implementing a recursive version of the `sum` method. Note that Viper does not allow method calls within compound expressions; a call to `sum` must have the form `x := sum(e)` for some variable `x` and expression `e`, and not, e.g `x := sum(e) + 42`. Does the same specification work also for your recursive implementation?
* Try implementing client code which calls the `sum` method in order to computes the sum of the first 5 natural numbers. Provide a suitable postcondition.

///

This tutorial gives an overview of the features of the Viper language and explains their syntax and semantics. We provide examples and exercises throughout, to illustrate the basic usage of these features. We encourage readers to experiment with the examples and often suggest variations of the presented examples to try out. The tutorial does not aim to explain the workings of the Viper verifiers in general, nor the advanced usage of Viper's language features for building custom verification tools: for these topics, we refer interested readers to our [Viper-related research papers](http://www.pm.inf.ethz.ch/research/viper.html).

If you have comments, questions or feedback about Viper, including this tutorial, we would be happy to receive them! Please send your emails to [viper@inf.ethz.ch](mailto:viper@inf.ethz.ch)
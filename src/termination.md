# Termination

In the context of Viper, reasoning about termination serves (at least) two purposes: the first is to prove that methods and loops terminate, the second is to ensure that Viper functions are *well-defined*. The second aspect is crucial even for front-ends that are not concerned with total correctness, because specifications, often expressed via Viper's pure functions, would be meaningless if the involved functions were not well-defined.

Front-ends can encode their own termination proofs, but since proving termination is a crucial verification task with subtle pitfalls, Viper has support for termination proofs built in, based on the well-known approach of *termination measures* (ranking functions).

> **Note**
>
> By default, i.e. if no termination measure is specified, then Viper won't check termination. This can be useful, e.g. if a front-end already performs or encodes its own termination checks.

In this section, we will introduce Viper's support for termination proofs: first, we describe how to specify termination measures, then we explain termination proofs for (mutually) recursive functions. Lastly, we discuss our *experimental* support for termination of [methods and loops](./termination-statement.md).

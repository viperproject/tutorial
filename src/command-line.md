# Command-Line Options

Both of Viper's verification backends can be configured via command-line options. When running a backend directly, the options are passed before the file to be verified, e.g.,

```
java -cp silicon.jar viper.silicon.SiliconRunner --timeout 60 --numberOfErrorsToReport 0 program.vpr
```

Options take their argument either separated by a space (`--timeout 60`) or by an equals sign (`--timeout=60`). Running a backend with `--help` prints the full list of options it supports; the most important ones are summarized below.

## General options

The following options are supported by both the Symbolic Execution (SE) backend and the Verification Condition Generation (VCG) backend.

### Verification and diagnostics

| Option | Description |
| ---- | ---- |
| `--counterexample <mode>` | Report a counterexample for each verification error. `resolved` yields a human-readable, backend-independent counterexample, in which heap resources are associated with the AST nodes they belong to; `raw` yields a backend-independent counterexample in which heap resources are keyed by backend-internal identifiers. The legacy modes `native` (the SMT solver's raw model), `variables` (values of all local Viper variables) and `mapped` (SE backend only) are also supported. |
| `--select <names>` | Verify only the given comma-separated methods, functions and predicates (e.g., `--select m1,f2,P`), together with the declarations they depend on. All other parts of the program are ignored. |
| `--reportPartialResults` | Report verification results for individual members (methods, functions, predicates) and branches as soon as they are available, instead of only reporting the overall result at the end. |

### Language semantics

The following options change the meaning of certain Viper constructs.

| Option | Description |
| ---- | ---- |
| `--respectFunctionPrePermAmounts` | Take precise permission amounts in [function preconditions](./functions.md) into account, instead of only requiring read access. |
| `--assumeInjectivityOnInhale` | Assume, rather than check, that the receiver expressions of [quantified permissions](./quantified-permissions-injectivity.md) are injective when they are inhaled. This makes inhaling (e.g., of preconditions) more permissive, but is unsound if the receiver expression is in fact not injective. |

### Plugins

Some language features are implemented as plugins that are enabled by default; further plugins can be loaded explicitly.

| Option | Description |
| ---- | ---- |
| `--disableTerminationPlugin` | Disable the [termination plugin](./termination.md), i.e., ignore `decreases` clauses. |
| `--disableAdtPlugin` | Disable the [ADT plugin](./domains-adt.md). |
| `--disableDefaultPlugins` | Disable all plugins that are enabled by default, including the termination and ADT plugins. |
| `--plugin <classes>` | Load additional plugins, given as fully-qualified class names separated by `:`. |
| `--enableSmokeDetection` | Insert `refute false` statements (see [assertion checking](./statements-assertions.md)) at various points of the program to detect unsound or inconsistent specifications, such as contradictory preconditions or unreachable code. |

## Options of the SE backend

### Timeouts

| Option | Description |
| ---- | ---- |
| `--timeout <n>` | Abort verification after approximately `n` seconds. The timeout applies to the whole verification run, not to individual methods (default: 0, i.e., no timeout). |
| `--assertTimeout <n>` | Timeout in milliseconds for each SMT query that checks a proof obligation (default: no timeout). If the solver times out, the assertion is reported as failing. Setting this option can turn non-terminating or very slow verification attempts into (possibly spurious) errors. |
| `--checkTimeout <n>` | Timeout in milliseconds for internal SMT queries that do not directly correspond to proof obligations, e.g., queries that check whether a branch is infeasible or whether two references alias (default: 10). Increasing this value can make verification more complete at the cost of performance. |
| `--proverEnableTimeBounds` | Use actual time limits for the timeouts above, rather than converting them to deterministic resource limits of the SMT solver (the default, which makes verification results more reproducible across machines). |
| `--z3ResourcesPerMillisecond <n>` | Conversion factor used to turn the timeouts above into Z3 resource limits (default: 10000). Larger values give the solver more work per millisecond of timeout. |
| `--cvc5ResourcesPerMillisecond <n>` | The same conversion factor for cvc5 (default: 50). |

### Error reporting

| Option | Description |
| ---- | ---- |
| `--numberOfErrorsToReport <n>` | Number of errors that are reported per method (or function, predicate) before verification of that member stops (default: 1). A value of 0 reports all errors. |
| `--enableBranchconditionReporting` | Include the branch conditions under which an error occurs in the error report. Useful for assertions that fail only on some paths. |
| `--reportReasonUnknown` | For each verification error, report the reason the SMT solver gave for being unable to prove the assertion (e.g., a timeout or incomplete quantifier instantiation). |

### Completeness and encoding choices

The SE backend makes a number of design choices that trade off completeness against performance. The following options adjust these choices; several of them can also be set for individual methods using [annotations](./language-annotations.md).

| Option | Description |
| ---- | ---- |
| `--exhaleMode <n>` | How permissions are removed when exhaling (and when evaluating expressions that require permissions). `0` (default) is a greedy mode that is fast, but can fail if the required permission is split across several heap chunks that may or may not alias. `1` uses a more complete algorithm that sums up permissions from all potentially-aliasing chunks. `2` uses the greedy mode first and retries with the more complete algorithm only if verification fails. In the SE backend, `--counterexample` requires mode 1. |
| `--exhaleModeQP <n>` | The same choice for [quantified permissions](./quantified-permissions.md); here, mode `1` is the default. |
| `--moreJoins <n>` | Whether to join execution paths after branching instead of verifying the rest of the method separately for each path. `0` (default) never joins, `1` joins branches resulting from impure conditionals (e.g., `b ==> acc(x.f)`), and `2` joins whenever possible. Joining can drastically reduce the number of paths in methods with many branches, but yields larger SMT queries. |
| `--maskHeapMode` | Use an alternative heap encoding based on total heap and permission maps (similar to the encoding of the VCG backend) rather than heap chunks. Not compatible with several other options, e.g., `--exhaleMode` and `--counterexample`. |
| `--simplifyOnConsume` | In `--maskHeapMode`, simplify the permission mask whenever permissions are removed, rather than just recording the subtraction. Only supported in combination with `--maskHeapMode`. |
| `--stateConsolidationMode <n>` | How eagerly the verifier merges heap chunks and derives facts from the current permissions (e.g., non-aliasing). `0` does minimal work, `1` (default) does the most work and is the most complete; the remaining modes are less eager variants (most of which consolidate only when retrying after a failure) and a mode intended for use with `--exhaleMode 1`. Run with `--help` for a description of all modes. |
| `--conditionalizePermissions` | Rewrite assertions such as `b ==> acc(x.f, p)` into `acc(x.f, b ? p : none)` to reduce the number of execution paths. Experimental. |
| `--enableSimplifiedUnfolds` | When verifying a predicate's well-formedness, record the resulting symbolic heap and assumptions for each branch of its body, and reuse them whenever the predicate is unfolded (via an `unfold` statement or an `unfolding` expression) instead of processing the body again. This can speed up programs with complex predicate bodies. |
| `--recursivePredicateUnfoldings <n>` | How many nested `unfolding` expressions are evaluated in the bodies of recursive predicates (default: 1). |
| `--alternativeFunctionVerificationOrder` | Compute the order in which functions are verified (and in which their definitional axioms become available) in a way that also takes dependencies between functions via predicate unfoldings into account. This is more complete for some programs, but less complete for others. |
| `--disableShortCircuitingEvaluations` | Disable short-circuiting evaluation of `&&` and `||` during well-definedness checks. For example, checking `i > 0 && f(i)` then fails if the precondition of `f` requires `i > 0`. |
| `--disableSubsumption` | Do not assume the asserted expression after a successful `assert` statement. |

### Debugging

| Option | Description |
| ---- | ---- |
| `--enableDebugging` | After verification, start an interactive debugger for the failed proof obligations. For a chosen failure, it shows the assumptions, heap chunks and branch conditions the verifier had at that point, and lets you add or remove assumptions, re-run the proof (optionally with a different SMT solver or timeout), and zoom in on individual assumptions to see where they came from. Not supported in combination with `--maskHeapMode`. |
| `--reportStateAfter <n>` | If no progress is made for approximately `n` seconds, report what the verifier is currently working on (current statement, outstanding solver queries, branch conditions). Helpful for diagnosing slow verification; not supported in combination with `--parallelizeBranches`. |
| `--printTranslatedProgram` | Print the final Viper program that is verified, i.e., after all plugins (e.g., for termination checking or ADTs) have transformed it. |
| `--enableTempDirectory` | Write the interaction with the SMT solver to SMT-LIB log files in the temporary directory. |
| `--tempDirectory <path>` | The temporary directory (default: `./tmp`). |
| `--proverLogFile <name>` | Write the SMT solver log to files starting with the given name (instead of the default location in the temporary directory). |
| `--printMethodCFGs` | Write the control-flow graph of each method as a DOT (Graphviz) file into the temporary directory. |
| `--logLevel <level>` | Set the logging level (`ALL`, `TRACE`, `DEBUG`, `INFO`, `WARN`, `ERROR` or `OFF`). |

### Prover and prover configuration

| Option | Description |
| ---- | ---- |
| `--prover <name>` | The SMT solver to use: `Z3` (default; Z3 run as a separate process), `cvc5`, or `Z3-API` (Z3 accessed via its Java API instead of a separate process). |
| `--z3Exe <path>` | Path to the Z3 executable used by Boogie. Alternatively, the environment variable `Z3_EXE` can be set. |
| `--cvc5Exe <path>` | Path to the cvc5 executable. Alternatively, the environment variable `CVC5_EXE` can be set. |
| `--proverConfigArgs "<k>=<v> ..."` | SMT solver configuration options, given as space-separated `key=value` pairs, e.g., `--proverConfigArgs "smt.qi.eager_threshold=100"`. These override the options the SE backend sets by default. |
| `--proverArgs "<args>"` | Command-line arguments that are passed on to the SMT solver. |
| `--proverRandomizeSeeds` | Set the SMT solver's random seeds to random values. Useful to check whether a successful verification is stable or only succeeds by chance. |
| `--disableNL` | Disable the solver's support for non-linear integer arithmetic (Z3 only). |

### Parallelisation

| Option | Description |
| ---- | ---- |
| `--numberOfParallelVerifiers <n>` | Number of methods that are verified in parallel, each using its own SMT solver instance (default: the number of available processors). Use 1 for sequential verification. |
| `--parallelizeBranches` | Additionally verify different branches of a method in parallel. |

## Options of the VCG backend

The VCG backend translates the Viper program into the [Boogie](https://github.com/boogie-org/boogie) intermediate verification language and runs the Boogie verifier on the result. Accordingly, its options mostly concern the interaction with Boogie.

### Timeouts

| Option | Description |
| ---- | ---- |
| `--timeout <n>` | Abort verification after approximately `n` seconds. The timeout applies to the whole Boogie run, not to individual methods (default: no timeout). |

### Debugging

| Option | Description |
| ---- | ---- |
| `--print <file>` | Write the generated Boogie program to the given file. This is useful to inspect the encoding, or to run Boogie on it manually. |
| `--proverLog <file>` | Write the SMT-LIB interaction between Boogie and Z3 to the given file. |

### Boogie and prover configuration

| Option | Description |
| ---- | ---- |
| `--boogieExe <path>` | Path to the Boogie executable. Alternatively, the environment variable `BOOGIE_EXE` can be set. |
| `--z3Exe <path>` | Path to the Z3 executable used by Boogie. Alternatively, the environment variable `Z3_EXE` can be set. |
| `--boogieOpt "<options>"` | Additional options that are passed on to Boogie, e.g., `--boogieOpt "/vcsCores:4"`. Options that change Boogie's output format are not supported. |

### Encoding choices

| Option | Description |
| ---- | ---- |
| `--desugarPolymorphicMaps` | Do not use polymorphic maps in the Boogie encoding, but desugar them into monomorphic ones. This can affect performance (in either direction). |
| `--disableAllocEncoding` | Do not generate assumptions about the allocation status of references. |

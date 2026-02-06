# Abstract Functions

Termination specifications may also be provided for abstract functions, i.e., those without a body. For such functions, Viper still checks that the specifications are well-defined, which includes that pre- and postconditions terminate. Moreover, when an abstract function is invoked, the previously described call-site checks are made.

When Viper performs a call-graph analysis to determine (mutually) recursive functions, abstract functions are assumed to not (mutually) recurse through their omitted bodies.

# Reference expressions

Reference-typed expressions denote either objects or the special value null (denoted by the `null` literal). The most important fact about `null` is the built-in assertion that permissions to fields of `null` cannot exist; Viper will deduce from holding a field permission that the receiver of the field location is non-null. The analogous assumption does not hold e.g. for predicate instances; it is possible for null to be the value of a predicate parameter.

# ADT plugin

```viper,editable,playground
adt List[T] {
    Nil()
    Cons(value: T, tail: List[T])
}
```

The ADT plugin is an extension to Viper that enables declarations of algebraic datatypes. These consist of one or more constructors, each of which has zero or more arguments. Any instance of such a datatype then corresponds to exactly one of these constructors. There is syntax to identify which constructor an instance corresponds to, as well as syntax to extract the arguments given to that constructor. As in the example above, ADTs can have type parameters and can be recursive.

Internally, the ADT syntax is translated into domains and domain function applications.

The plugin is enabled by default, and can be disabled with the command-line option `--disableAdtPlugin`.

## Discriminators

For every constructor of the ADT, a *discriminator* is generated. Syntactically, this is a field with the name `is<Constructor>` with a `Bool` type.

```viper
assert Cons(1, Cons(2, Nil())).isCons
assert Nil().isNil
```

## Destructors

For every argument of every constructor of the ADT, a *destructor* is generated. This is a field that extracts the given argument out of the constructor, and is only well-defined if the ADT instance is known to correspond to the given constructor.

```viper
assert Cons(1, Nil()).value == 1
assert Cons(1, Nil()).tail == Nil()

// this expression is not well-defined:
// assert Nil().value == 0
```

## Derived methods

Similarly to derivable methods in Haskell or Rust, the ADT plugin provides a syntax to derive certain operations for ADTs.

```viper
import <adt/derives.vpr>

adt Name[...] {
    ...
} derives {
    ...
}
```

The block after the `derives` keyword is a list of functions that should be derived for the declared ADT. At the moment, the only supported operation is `contains`, but this may change in future Viper versions.

Note that the `import <adt/derives.vpr>` is required for derived methods to work.

## `contains`

When the `contains` operation is derived, the function `contains` becomes available for the given ADT. Given a value and an ADT instance, it evaluates to `true` if the former value is found inside the ADT instance, as one of its constructor arguments. This evaluation works recursively.

```viper,editable,playground
import <adt/derives.vpr>

adt List[T] {
    Nil()
    Cons(value: T, tail: List[T])
} derives {
    contains
}

method client() {
    var x: List[Int] := Cons(42, Cons(33, Nil()))

    // test for the "value" argument of type Int in x
    assert contains(42, x)
    assert contains(33, x)

    // test for the "tail" argument of type List[Int] in x
    assert contains((Nil() : List[Int]), x)
    assert contains(Cons(33, Nil()), x)
}
```

By default, all arguments of every constructor of an ADT are considered for the `contains` operation. An optional comma-separated blocklist of arguments can be declared, which will cause the `contains` operation to ignore the named arguments:

```viper,editable,playground
import <adt/derives.vpr>

adt Tree[T] {
    Leaf()
    Node(left: Tree[T], val: T, right: Tree[T])
} derives {
    contains without left, right
}

method client() {
    var x: Tree[Int] := Node(Leaf(), 42, Node(Leaf(), 33, Leaf()))
    assert contains(42, x)

    // will fail to prove, because "right" is in the blocklist
    assert contains(Node(Leaf(), 33, Leaf()), x)
}
```

# General Syntax of `decreases` Tuples

In the previous examples, the termination measures were always single expressions. However, it is not always possible to find a single expression whose value decreases at each call, and Viper therefore also supports tuples of expressions as termination measures. The well-founded order for tuples is the lexicographical order over the tuple elements.

More precisely, let `(a1, a2, ...)` and `(b1, b2, ...)` be two non-empty tuples of finite (and for now, equal) length. The well-founded order `<_` that is used to compare the two tuples is defined as follows:

```plain
(a1, a2, ...) <_ (b1, b2, ...)
    <==>
a1 <_ b1  ||  a1 == b1 && (a2, ...) <_ (b2, ...) 
```

Special cases, such as empty tuples, tuples of different length, and tuples of different types will be discussed later.

A typical example of a function for which a tuple as termination measure is used, is the Ackermann function:

```viper,editable,playground
function ack(m:Int, n:Int):Int
  decreases m, n
  requires m >= 0
  requires n >= 0
  ensures result >= 0
{
  m == 0 ? n + 1 :
  n == 0 ? ack(m - 1, 1) :
           ack(m - 1, ack(m, n - 1))
}
```

For the first recursive call `ack(m - 1, 1)`, and the second (outer) recursive call `ack(m - 1, ack(m, n - 1))`, the first expression of the tuple (i.e. `m`) decreases. Hence, the other part of the tuple is not required to decrease in this situation. In the third (inner) recursive call `ack(m, n - 1)` the first expression of the tuple is unchanged, while the second tuple expression (i.e., `n`) decreases.

> **Exercise**
>
> Swap the tuple elements, i.e., change the decreases clause to `n, m`. For which of the recursive calls do you expect error messages?

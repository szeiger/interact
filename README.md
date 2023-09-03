# Language, interpreter and compiler for interaction nets

The language implements interaction nets and combinators as defined in https://core.ac.uk/download/pdf/81113716.pdf.

## Running

Launch `sbt` and then `runMain Main example.in` in the sbt shell to run [example.in](./example.in) using a single-threaded interpreter.

Launch `sbt` and then `runMain Debug example.in` in the sbt shell to run [example.in](./example.in) using the step-by-step debugger.

## Language

There are 4 basic statements: `cons` defines a data constructor, `def` defines a function (with optional rules), `match` defines a detached rule, and `let` creates a part of the net that should be evaluated. Comments start with `#` and extend until the end of the line. Expression lists use Haskell-style significant indentation.

### Constructors

Constructors are written as `Id(aux_1, aux_2, ..., aux_n) = principal`. The parentheses are optional for arity 0. The prinpical port is only used for documentation purposes and can always be omitted. For example:

```
# Natural numbers
cons Z
cons S(n)
```

### Functions

Semantically there is no difference between data and code, and it is possible to define and use functions with the normal constructor syntax and detached rules (or conversely use function syntax for data). A separate syntax exists because it makes sense for data to have the principal port be the return value of the expression, but it is more useful for functions to have the principal port as a parameter:

```
def add(x, y) = r
```

The first argument of the function is always assigned to the principal port while the rest of the arguments and return value(s) make up the auxiliary ports. Note that return values must always be specified for functions because their arity is not fixed (like it is for constructors). Tuple syntax is used for multiple return values, e.g.:

```
def dup(x) = (a, b)
```

In order to define rules together with the function, the parameters and return values must be named. The first argument (i.e. the principal port) can be always omitted by using a `_` wildcard:

```
def add(_, y) = r
```

Other parameters can be omitted if the rules don't need them (because they use curried patterns or are defined as detached rules).

### Data

The interaction nets that should be reduced by the interpreter are defined using `let` statements:

```
let two = S(S(Z))
    y = S(S(S(S(S(Z)))))
    x = S(S(S(Z)))
    example_3_plus_5 = add(x, y)
```

The body of a `let` statement contains a block of expressions consisting of assignments and nested function / constructor applications. Tuples can be used to group individual values, but they cannot be nested. Variables that are used exactly once are defined as free wires. Additional temporary variables can be introduced, but they must be used exactly twice. The order of expressions and the direction of assignments is irrelevant.

The syntax for expression blocks uses Haskell-style layout: Additional expressions must start at the same indentation level as the first one. Lines with larger indentation continue the current expression. Multiple exressions on the same line must be separated by `;`. A trailing `;` at the end of the line is optional. 

### Operators

Both, constructors and functions, can be written as symbolic binary operators. An operator consists of an arbitrary combination of the symbols `*/%+-:<>&^|`. Precedence is based on the first character (the same as in Scala), operators ending with `:` are right-associative, all others left-associative (again, like in Scala). All operators in a chain of same-precedence operations must have the same associativity. Operator definitions are written in infix syntax:

```
# Linked lists
cons Nil
cons head :: tail

def _ + y = r
```

The same infix notation is used for applying them in expressions:

```
let example_3_plus_2 = S(S(S(Z))) + S(S(Z))
```

### Rules

Reduction rules for functions can be specified together with the definition using a pattern matching syntax which matches on the first argument:

```
# Addition on natural numbers
def _ + y = r
  | Z    => y
  | S(x) => r = x + S(y)
```

The right-hand side contains an expression list, similar to a `let` clause. All function/constructor arguments and return values (except the principal port on each side of the match) must be used exactly once in the reduction.

```
def _ * y = r
  | Z    => erase(y)
            Z = r
  | S(x) => (y1, y2) = dup(y)
            x * y1 + y2 = r
```

If the last expression in the block is missing an assignment, it is implicitly assigned to the return value of the function:

```
def _ + y = r
  | Z    => y           # same as y = r
  | S(x) => x + S(y)    # same as x + S(y) = r
```

The standard `dup` and `erase` functions are pre-defined, and combinators with all user-defined constructors and functions are derived automatically. The pre-defined functions are equivalent to the following syntax:

```
def erase(_) = ()
def dup(x) = (x1, x2)
```

When matching on another function instead of a constructor, a `_` wildcard must be used to mark the first argument (i.e. the principal port) as the designated return value of an assignment expression. The wildcard always expands to the return value of the nearest enclosing assignment. For example: 

```
def dup(_) = (a, b)
  | dup(_) = (c, d) => (c, d)
```

When matching on a function with no return value (like `erase`), an assignment to an empty tuple can be used to correctly expand the wildcard:

```
def erase(_)
  | erase(_) = () => ()
```

### Currying

It is possible to use both, nested patterns and additional matches on auxiliary ports, to define curried functions, corresponding to currying on the left-hand side and right-hand side of a match. For example:

```
def fib(_) = r
  | Z       => 1n
  | S(Z)    => 1n
  | S(S(n)) => (n1, n2) = dup(n)
               fib(S(n1)) + fib(n2)
```

This expands to a definition similar to this one (modulo the generated name of the curried function):

```
def fib(_) = r
  | Z    => 1n
  | S(n) => fib2(n)

def fib2(_) = r
  | Z    => 1n
  | S(n) => (n1, n2) = dup(n)
            fib(S(n1)) + fib(n2)
```

Matching on auxiliary ports is done by specifying a comma-separated list in a `def` rule. In the following example `b` is matched by `S(y)` in the second rule after successfully matching `a` with `S(x)`:

```
def foo(a, b) = r
  | Z           => erase(b), Z
  | S(x), S(y)  => x + y
```

Restrictions on curried rules:
- All additional matches must be done on the same port of the original match.
- Nested matches must not conflict with another match at the outer layer (e.g. you cannot match on both `f(S(x))` and `f(S(S(x)))`). 

### Detached Rules

A rule can be defined independently of a function definition using a `match` statement. These rules can also be defined for `cons`-style constructors (which do not have a special rule syntax like `def`). The expression on the left-hand side is interpreted as a pattern which must correspond to two cells connected via their principal ports. For example:

```
match add(Z, y) => y
match add(S(x), y) => add(x, S(y))
```

A combination of two constructors can be matched with an assignment, e.g.:

```
# Assimilation rules for S and dup
match S(x) = S(y) => x = y
match dup(dup(_) = (c, d)) = (a, b) => (c, d)
```

Currying works the same as in rules attached to a `def` statement.

### Natural Numbers

There is syntactic support for parsing and printing natural numbers, e.g.:

```
let example_3_times_2 = mult(3n, 2n)
```

The snippet expands to:

```
let example_3_times_2 = mult(S(S(S(Z))), S(S(Z)))
```

This assumes that you have suitable definitions of `Z` and `S` like:

```
cons Z
cons S(n)
```

### Embedded Values

A cell (`cons` or `def`) can optionally contain a primitive JVM value of type `int`, `ref` (`java.lang.Object`) or `label`. The type is placed in square brackets after the constructor name:

```
cons Int[int]
cons String[ref]
```

Any match on such a constructor or its use in an expression must associate a variable name with the embedded value. These embedded variables share the same scope as regular variables but cannot be used interchangeably. If the same variable is used in a match and in the expansion, the value is automatically moved:

```
def _ + y = r
  | Int[i] => intAdd[i](y)
```

`int` and `label` values can also be copied or deleted implicitly by using the variable assigned to them in the match more or less than once in the expansion. `ref` values can only be moved implicitly.

A static JVM method (or a method in a Scala object) can be invoked to perform a computation on embedded values by calling the method with its fully qualified name in an embedded expression in square brackets:
```
def intAdd[int a](_) = r
  | Int[b] => [de.szeiger.interact.Intrinsics.add(a, b, c)]
              Int[c]
```

Input parameters (corresponding to variables used in the match) must be of type `int` or a reference type, output parameters (corresponding to variables used in the expansion) must be of type `IntBox` or `RefBox`:

```
// Implementation in Scala:
object Intrinsics {
  def add(a: Int, b: Int, res: IntBox): Unit =
    res.setValue(a + b)
}
```

It is up to the implementation of such a method to handle copying and deleting in an appropriate way. Since embedded `ref` values can also be copied and deleted by the `dup` and `erase` functions, the values may implement the `LifecycleManaged` interface to implement these methods. Otherwise, references will be shared or dropped from scope as usual on the JVM.

An implementation method may directly return a value instead of using an `IntBox` / `RefBox` output parameter. Such a method can be used directly as an embedded computation of a cell:

```
def strlen(_) = r
  | String[s] => Int[de.szeiger.interact.Intrinsics.strlen(s)]
```

Int literals and some basic operators are available in embedded computations, e.g.:

```
let x = Int[3 + 5]
```

Embedded values can be checked in a match to select different expansions for a rule depending on the embedded values:

```
def fib(_) = r
  | Int[i] if [i == 0]  => Int[1]
           if [i == 1]  => Int[1]
           else         => fib(Int[i-1]) + fib(Int[i-2])
```

The `else` clause is required, all branches must be defined together, and the order of definition is significant.

Current implementation limitations:
- Currying is not allowed when both sides of the match contain embedded values.
- Only the `st3.i` interpreter back-end supports embedded values.

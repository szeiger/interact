# Language, interpreter and compiler for interaction nets

The language implements interaction nets and combinators as defined in https://core.ac.uk/download/pdf/81113716.pdf.

## Running

Launch `sbt` and then `runMain Main example.in` in the sbt shell to process [example.in](./example.in) using a single-threaded interpreter.

## Language

There are 4 basic statements: `cons` defines a data constructor, `let` defines a function (with optional rules), `match` defines a detached rule, and `let` creates a part of the net that should be evaluated. Comments start with `#` and extend until the end of the line. There are no statement separators and no significant whitespace.

### Constructors

Constructors are written as `Id(aux_1, aux_2, ..., aux_n)`. The parentheses are optional for arity 0. For example:

```
# Church numerals
cons Z
cons S(n)
```

Since every constructor has one principal port there is no need to name it, but it can be done for documentation purposes:

```
cons Z: result
cons S(n): result
```

### Functions

Semantically there is no difference between data and code, and it is possible to define and use functions with the normal constructor syntax and detached rules (or conversely use function syntax for data). A separate syntax exists because it makes sense for data to have the principal port be the return value of the expression, but it is more useful for functions to have the prinpical port as a parameter:

```
def add(x, y): r
```

The first argument of the function is always assigned to the principal port while the rest of the arguments and return value(s) make up the auxiliary ports. Note that return values must always be specified for functions because their arity is not fixed (like it is for constructors). Tuple syntax is used for multiple return values, e.g.:

```
def dup(x): (a, b)
```

In order to define rules together with the function all parameters and return values must be named. The first argument (i.e. the principal port) can be omitted by using a `_` wildcard:

```
def add(_, y): r
```

### Data

The nets that should be reduced by the interpreter are defined using `let` statements:

```
let two = S(S(Z)),
    y = S(S(S(S(S(Z))))),
    x = S(S(S(Z))),
    example_3_plus_5 = add(x, y)
```

The body of a `let` statement contains assignments and nested function / constructor applications separated by commas. Tuples can be used to group individual values, but they cannot be nested. Variables that are used exactly once are defined as free wires. Additional temporary variables can be introduced, but they must be used exactly twice. The order of statements and the direction of assignments is irrelevant.

### Rules

Reduction rules for functions can be specified together with the definition using a pattern matching syntax which always matches exclusively on the first argument:

```
def add(_, y): r
  | Z    => y
  | S(x) => r = add(x, S(y))
```

The right-hand side is similar to a `let` body. All function/constructor arguments and return values (except the princpipal port on each side of the match) must be used exactly once in the reduction.

```
def mult(_, y): r
  | Z    => erase(y),
            Z
  | S(x) => (y1, y2) = dup(y),
            add(mult(x, y1), y2) = r
```

If the last expression is missing an assignment, it is implicitly assigned to the return value of the function:

```
def add(_, y): r
  | Z    => y
  | S(x) => add(x, S(y))
```

The standard `dup` and `erase` functions are pre-defined, and combinators with all user-defined constructors and functions are derived automatically. The pre-defined functions are equivalent to this syntax:

```
def erase(_): ()
def dup(_): (a, b)
```

When matching on another function instead of a constructor, a `_` wildcard must be used to mark the first argument (i.e. the principal port) as the designated return value of an assignment expression. For example: 

```
def dup(_): (a, b)
  | dup(_) = (c, d) => (c, d)
```

### Detached Rules

A rule can be defined independently of a function definition using a `match` statement. The expression on the left-hand side is interpreted as a pattern which must correspond to two cells connected via their principal ports. For example:

```
match add(Z, y) => y
match add(S(x), y) => add(x, S(y))
```

A combination of two constructors can be matched with an assignment, e.g.:

```
match S(x) = S(y) => x = y
```

It is currently not possible to use nested assignments with wildcards (which are required to match a combination of two functions).

### Church numerals

There is syntactic support for parsing and printing church numerals, e.g.:

```
let example_3_times_2 = mult(3'c, 2'c)
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

### Lists

There is syntactic support for parsing and printing lists, e.g.:

```
let list_1_2_3 = 1'c :: 2'c :: 3'c :: Nil
```

The snippet expands to:

```
let list_1_2_3 = Cons(1'c, Cons(2'c, Cons(3'c, Nil)))
```

This assumes that you have a suitable definitions of `Cons` and `Nil` like:

```
cons Nil
cons Cons(head, tail) . l
```

# Language and interpreter for interaction nets

The interpreter implements interaction nets and combinators as defined in https://core.ac.uk/download/pdf/81113716.pdf.

## Running

There is no proper command line at the moment. Edit `test.in` with your changes, launch `sbt` and then `run` the main class.

## Language

There are 3 basic statements: `cons` defines a constructor (with associated rules), `rule` defines a detached rule, and `let` creates a part of the net that should be evaluated. Comments start with `#` and extend until the end of the line. There are no statement separators and no significant whitespace.

### Constructors

Constructors are written as `Id(aux_1, aux_2, ..., aux_n)`. The parentheses are optional for arity 0. For example:

```
# Church numerals
cons Z
cons S(n)
```

Since every constructor has a principal port there is no need to name it, but it can be done for documentation purposes using "cut" syntax:

```
cons Z . result
cons S(n) . result
```

### Nets

The nets that should be reduced by the interpreter are defined using `let` clauses:

```
let two, example_3_plus_5 =
  two . S(S(Z)),
  y . S(S(S(S(S(Z))))),
  x . S(S(S(Z))),
  Add(y, example_3_plus_5) . x
```

The body of the `let` clause is a list of cuts (`a . b` where a and b are expressions that are connected via their principal ports). The basic expressions are identifiers (for nullary constructors (usually capitalized), free ports, or local wires) or applications of constructors (which connect the principal port of an argument to an auxiliary port of the constructor). Local wires may be introduced in a `let` clause (`x` and `y` in the previous snippet). They must be used in a linear way, i.e. they occur exactly twice in the clause. The left-hand side of the `let` clause lists its free ports (`two` and `example_3_plus_5` in the previous snippet). They must be used exactly once in the body. Note that cuts are always symmetric, i.e. `a . b` is the same as `b . a`.

### Rules

All rules are defined on a cut. Detached rules use a cut pattern that names the ports on the left-hand side and has a list of cuts as the replacement on the right-hand side:

```
rule Dup(a, b) . Z  = a . Z, b . Z
rule Dup(a, b) . S(x) = x . Dup(sa, sb),
                        a . S(sa), b . S(sb)
```

All port names in the pattern must be unique, and their use across the combination of the pattern and the replacement must be linear (i.e. they are treated as free ports in the replacement). Like in `let` clauses, the replacement may introduce local wires.

Rules can be defined in a simpler way together with one of their constructors using a `cut` clause. This avoids repeating the constructor name and assigning names to the ports in a pattern match. Instead the auxiliary ports use the names defined in the constructor:

```
cons Dup(a, b)
  cut Z  = a . Z, b . Z
  cut S(x) = x . Dup(sa, sb), a . S(sa), b . S(sb)
```

### Rule derivation

Rules that reduce a cut of a constructor and the standard `Erase` and `Dup` combinators can be derived automatically using a `deriving` clause:

```
cons Add(y, r) . x
  deriving Erase, Dup
```

The above example is equivalent to:

```
cons Add(y, r) . x
  cut Erase = y . Erase, r . Erase
  cut Dup(a, b) = a . Add(s2, s3),
                  b . Add(s4, s5),
                  y . Dup(s2, s4),
                  r . Dup(s3, s5)
```

Note that this expansion is purely syntactical. You still need to define suitable `Dup` and `Erase` constructors by yourself, e.g.:

```
cons Erase                   deriving Erase
cons Dup(a, b) . in          deriving Erase
  cut Dup(c, d) = a . c, b . d
```

### Church numerals

There is syntactic support for parsing and printing church numerals, e.g.:

```
let example_3_times_2 =
  Mult(2'c, example_3_times_2) . 3'c
```

The snippet expands to:

```
let example_3_times_2 =
  Mult(S(S(Z)), example_3_times_2) . S(S(S(Z)))
```

This assumes that you have suitable definitions of `Z` and `S` like:

```
cons Z                       deriving Erase, Dup
cons S(n)                    deriving Erase, Dup
```

### Lists

There is syntactic support for parsing and printing lists, e.g.:

```
let list_1_2_3 =
  1'c :: 2'c :: 3'c :: Nil
```

The snippet expands to:

```
let list_1_2_3 =
  Cons(1'c, Cons(2'c, Cons(3'c, Nil)))
```

This assumes that you have a suitable definitions of `Cons` like:

```
cons Nil                     deriving Erase, Dup
cons Cons(head, tail) . l    deriving Erase, Dup
```

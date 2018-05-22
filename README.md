# Stoic

The purpose of this project is to explore the theoretical foundation
as well as conceptual possibilities of *capability-based systems*.

A main trait of the calculi under study is the introduction of
_stoic functions_. Compared to normal functions which can capture
anything from the environment, _stoic functions_ don't capture
capabilities or _non-stoic functions_ from the environment. In
this sense, they are capability-disciplined.

There are two major applications of the calculus:

- capability-based effect systems
- capability-based security

## Capability-based Effect System

The core idea is that capabilities are required to produce side effects,
thus by tracking capabilities in the type system it's possible to
track side effects in the type system. To make sure capabilities are
passed by function parameters instead of being captured from the
environment, we need to resort to *stoic functions*.

Compared to existing type-and-effect systems(Gifford and Lucassen,
[1986](http://dl.acm.org/citation.cfm?id=319848),
[1988](http://dl.acm.org/citation.cfm?id=73564)) and monad-based
effect systems, capability-based effect systems have the advantage of
more succinct syntax and lower cognitive load in handling of effect
polymorphism. Thus capability-based effect systems stand a better
chance to be adopted by programmers.

For example, in the following example, the type system would report an
error on `foo`, as it's not allowed to capture any capability
variables in the environment:

``` scala
def map(xs: List[Int], f: Int => Int): List[Int]
def pmap(xs: List[Int], f: Int -> Int): List[Int]                //  -> means f is stoic function type
def print(x: Any)(implicit c: IO): ()

def bar(xs: List[Int])(implicit c: IO) = {
    map(xs, { x => print(x); x })
}

def foo(xs: List[Int])(implicit c: IO) = {
    pmap(xs, { x => print(x); x })                              // Error, can't capture c:IO
}
```

In the code above, `map` allows the passed in function `f` to have any
side effects, while `pmap` forbids any side effects.

If the designer of `pmap` wants the passed function `f` to only have
input/output side effects, he can simply adapt the signature of `pmap`
as follows:

``` scala
def pmap(xs: List[Int], f: Int -> IO -> Int)(implicit c: IO): List[Int]

def foo(xs: List[Int])(implicit c: IO) = {
    pmap(xs, { x => c => print(x)(c); x })                       // capability c is passed in by pmap
}
```

This way, the designers of APIs can strictly control what side effects
a passed in function can have.

## Capability-base Security

_Stoic functions_ lend itself as a powerful conceptual tool in
designing and reasoning security protection in capability-based systems.

For example, KeyKos is the first capability-based operating system
that implements _confinement_. Roughly speaking, _confinement_ means a
user is able to use a potentially malicious program from an unknown
source to process his sensitive data without worrying that the
malicious program will leak the data.

While KeyKos is a very powerful and secure system
(UNIX/Linux/Windows/OSX will never match), the concepts in KeyKos are
not easy to understand, for instance it has concepts like _factory_,
_discreet_ and _sensory capabilities_, to name just a few. _Stoic
functions_ help clarify the concepts and reason the design of the
system. It is our hypothesis that any capability-based operating
system has to implement a primitive similar to _stoic functions_ in
order to enable useful security patterns.

We also believe _stoic functions_ will be useful in designing security
protection in open ecosystems, like
[Caja](https://developers.google.com/caja/), cloud-based computing
platforms and app security in mobile phones.

## Concepts

A **capability** is a term of type `E`. The **base type** is
represented as `B`.

A **pure environment** is a subset of the ordinary typing environment,
which particularly excludes variables of ordinary function types,
variables of capability types and so on. Different systems may differ
in details about what types can be kept in the *pure environment*,
though they must all be *effect-safe*. Note that the pure environment
may contain variables of uninhabited types, such as `All X.X`, `B
-> E` and so on. These uninhabited types doesn't pose a problem,
as from absurdity everything follows (*ex falso quodlibet*).

A **stoic function** is a function that can be typed in *pure
environment*. Its type is represented by `A -> B`.

A **free function** is a function which can capture anything in the
lexical scope.  Its type is represented by `A => B`.

A type T is **inhabited** if there exists a value v which can be
typed as T under the environment {x:B, y:E} (note: variables are
values).

An **inhabited environment** is an environment with only variables
of inhabitable types.

A capability-based system is **cpability-safe** if a stoic function
can only use explicitly or implicitly (via free functions) given
capabilities. It cannot use any other capabilities directly or
indirectly.

This guarantee is the same as that in a **pure** and **inhabited**
environment (1) it’s impossible to construct a term of capability
type `E`; (2) it's impossible to construct an application where
the first term is not stoic.

A **capsafe environment** is a construct to help prove effect
safety. The intended relation between "pure", "inhabited" and
"capsafe" environment is as follows:

> A pure and inhabited environment is also a capsafe (and pure)
> environment.

## Publication

1. [A Study of Capability-Based Effect Systems](https://infoscience.epfl.ch/record/219173?ln=en), *F. Liu, S. Stucki (dir), N. Amin(dir)*, master thesis, EPFL, 2016

## Reference

1. [Spores](http://infoscience.epfl.ch/record/191239)  *Heather Miller et al*, 2014
2. [Software Foundations](http://www.cis.upenn.edu/~bcpierce/sf)  *Benjamin C. Pierce et al*
3. [Types and programming languages](https://www.cis.upenn.edu/~bcpierce/tapl/)  *Benjamin C. Pierce*
4. [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/)  *Adam Chlipala*
5. [Locally Nameless](http://www.chargueraud.org/softs/ln/)  *Arthur Charguéraud*
6. [TLC](http://www.chargueraud.org/softs/tlc/)  *Arthur Charguéraud*
7. [Integrating functional and imperative programming](http://dl.acm.org/citation.cfm?id=319848)  *D. K. Gifford & J. M. Lucassen*, 1986
8. [Polymorphic effect systems](http://dl.acm.org/citation.cfm?id=73564)  *J. M. Lucassen & D. K. Gifford*, 1988
9. [Witnessing Purity, Constancy and Mutability](http://link.springer.com/chapter/10.1007/978-3-642-10672-9_9)  *Ben Lippmeier*, 2009
10. [The marriage of effects and monads](http://dl.acm.org/citation.cfm?id=289429) *Philip Wadler*, 1999
11. [Type and Effect Systems](http://www2.imm.dtu.dk/~fnie/Papers/NiNi99tes.pdf)  *Flemming Nielson & Hanne Riis Nielson*, 1999

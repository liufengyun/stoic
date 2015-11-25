# Typed Closure

The purpose of this project is to construct a sound and effect-safe
type-and-effect system based on *capabilities*.

The core idea is to introduce *capability types* and *effect-closed
functions* explicitly in the system.  Compared to ordinary functions,
*effect-closed functions* are not allowed to capture variables of
capability types in the lexial scope, as well as variables of ordinary
function types.

## Motivation

Compared to existing effect systems in the literature(Gifford and
Lucassen, [1986](http://dl.acm.org/citation.cfm?id=319848),
[1988](http://dl.acm.org/citation.cfm?id=73564)), capability-based
effect systems have the advantage of more succinct syntax and better
handling of effect polymorphism. Thus capability-based effect systems
stand a better chance to be adopted by programmers.

In a capability-based effect system, effects can be controlled via
effect-closed functions. Effect-closed functions cannot capture any
capability variables in the outer lexical scope or variables of
ordinary function types that might have potential side effects. To
have side effects, the capability instances or ordinary functions must
be passed in as parameters by the caller, thus visible from type
signature and can be controlled by the caller.

For example, in the following example, the type system would report an
error on `foo`, as it's not allowed to capture any capability
variables in the environment:

``` scala
def map(xs: List[Int], f: Int => Int): List[Int]
def pmap(xs: List[Int], f: Int -> Int): List[Int]                //  => means f is effect-closed
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

## Concepts

A **capability** is a term of type `E`. The **base type** is
represented as `B`.

An **effect-closed typing environment** is a subset of the ordinary
typing environment, which particularly excludes variables of ordinary
function types, variables of capability types and so on. Different
systems may differ in details about what types can be kept in the
*effect-closed typing environment*, though they must all be
*effect-safe*. Note that the effect-closed typing environment may
contain variables of ill types (un-inhabitable), such as `All X.X`, `B
-> E` and so on. These ill types doesn't pose a problem, as from
absurdity everything follows(ex falso quodlibet).

An **effect-closed term abstraction** is a term abstraction that can
be typed in *effect-closed typing environment*. Its type is represented by `A
-> B`.

An **effect-closed type abstraction** is a term that can be typed in
*effect-closed typing environment*. Its type is represented by `All_Closed
X.T`.

An **ordinary term abstraction** is a term abstraction which can
capture anything in the lexical scope.  Its type is represented by `A
=> B`.

An **ordinary type abstraction** is a type abstraction which can
capture anything in the lexical scope. Its type is represented by `All
X.T`.

A **healthy environment** is an *effect-closed typing environment*
where it does not contain variables of ill types (un-inhabitable),
such as `All X.X`, `B -> E` and so on. As a meta-theory, it's
important to prove that **the formulation of healthy environment
should only reject ill types(un-inhabitable)**. It's incorrect to
reject inhabitable types, but it's OK to keep ill types, as long as
effect safety can be proved. For example, in our formulation the
presence of the un-inhabitable type `E -> B -> E` in healthy
environment does not endanger effect safety.

A capability-based type-and-effect system is **effect-safe** if from a
**healthy environment** (1) it’s impossible to construct a term of
type `E`; (2) it's impossible to construct an application where the
first term is not effect-closed; (3) it's impossible to construct a
type application where the first term is not effect-closed.


## Steps

| Milestones                                |          Description                                   |         status      |
| ----------------------------------------- | ------------------------------------------------------ | --------------------|
|  **Phase 1**                              |    **Warm Up**                                         |                     |
|  [stlc_cfun_ln.v](stlc_cfun_ln.v)         |    STLC + closed functions                             |      Finished       |
|  [f_cfun_ln.v](f_cfun_ln.v)               |    F + closed functions                                |      Finished       |
|  [f_cfun_ln_v2.v](f_cfun_ln_v2.v)         |    F + closed functions(type variable capture)         |      Finished       |
|  [fsub_cfuns_ln.v](fsub_cfuns_ln.v)       |    F<: + closed functions                              |      Finished       |
|  [fsub_cfuns_ln_v2.v](fsub_cfuns_ln_v2.v) |    F<: + closed functions(type variable capture)       |      Finished       |
|  **Phase 2**                              |    **Pure Capability**                                 |                     |
|  [stlc_cap_pure.v](stlc_cap_pure.v)       |    STLC + capabilities                                 |      Finished       |
|  [f_cap_pure.v](f_cap_pure.v)             |    F + capabilities                                    |      Finished       |
|  [f_cap_pure_v2.v](f_cap_pure_v2.v)       |    F + capabilities(allow B->E to type app)            |      Finished       |
|  **Phase 3**                              |    **Pure Capability + Subtyping**                     |                     |
|  [stlc_cap_sub_pure.v](stlc_cap_sub_pure.v) |    STLC + capabilities + subtyping                   |      Finished       |
|  fsub_cap_pure.v                          |    F<: + capabilities                                  |      -              |
|  **Phase 4**                              |    **Impure Capability + Subtyping**                   |                     |
|  [stlc_cap_impure.v](stlc_cap_impure.v)   |    STLC + capabilities + =>                            |      Working        |
|  fsub_cap_impure.v                        |    F<: + capabilities + =>                             |      -              |


## Development

Prerequisite: Install `Coq v8.5beta2`.

### Get Started

1. clone the repo: `git clone git@github.com:liufengyun/typed-closure.git`
1. init submodules: `git submodule init`
1. compile libs: `make lib`
1. compile project: `make`

### Makefile Tasks

- compile project: `make`
- clean project: `make clean`
- compile libs: `make lib`
- clean lib: `make libclean`

### Tips about Coq Version

A `settings.sh` file can be used to specify the version of Coq to use:

    COQBIN=/path/to/coq/bin/

If you do this, please also put a copy of `settings.sh` under `lib/tlc/src/`.

### Compile Locally Nameless

The locally-nameless project under `lib/ln/ln` is not compiled by default,
as it's not required for compiling current project. Follow the steps below
to compile the project if needed:

First, put a `settings.sh` file under `lib/ln/ln`:

``` shell
TLC=../../tlc/src/
COQBIN=/path/to/coq/bin/
```

Then, run `make`.

If you want to play with `locally-nameless` interactively in emacs,
put a `.dir-locals.el` file under `lib/ln/ln`:

    ((coq-mode . ((coq-prog-args . ("-emacs-U" "-R" "../tlc/src" "TLC")))))

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

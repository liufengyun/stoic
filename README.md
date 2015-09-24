# Typed Closure

The purpose of this project is to provide a sound type system
to control effects of closures.

## Motivation

The primary concern of this project is to provide a type-safe solution
for distributed data-parallel computation like
[Spark](https://spark.apache.org), where sending a function over the
wire is very common.

When sending a function over the wire, it's important to defend
against following closure-related hazards:

1. accidental capture of non-serializable variables(including `this`)
2. capturing references to mutable objects
3. unwanted transitive references
4. the function has no side effect or its side effect can be controlled
  (via type system)

[Spores](http://infoscience.epfl.ch/record/191239) provide a type-safe
abstraction to deal with the first three problems. This project
focuses on the last problem, namely to control side effects of
closures based on a type system.

For example, in the following example, the type system would report an
error on `foo`, as it's not allowed to capture any variables in the
environment, including `c`(but also `print`?):

``` scala
def map(xs: List[Int], f: Int => Int)(implicit c: IO): List[Int]
def pmap(xs: List[Int], f: Int (=>) Int): List[Int]                //  (=>) means f is closed
def print(x: Any)(implicit c: IO): ()

def bar(xs: List[Int])(implicit c: IO) = {
    map(xs, { x => print(x); x })
}

def foo(xs: List[Int])(implicit c: IO) = {
    pmap(xs, { x => print(x); x })
}
```

## Steps

| Milestones                   |          Description             |         status      |
| ---------------------------- | -------------------------------- | --------------------|
|  Milestone 1                 |    STLC + closed functions       |      Finished       |
|  Milestone 2                 |    System F + closed functions   |                     |
|  ...                         |                                  |                     |

## Development

Make sure `Coq v8.5beta2` is used.

1. clone the reop: `git clone git@github.com:liufengyun/typed-closure.git`
1. init submodules: `git submodule init`
1. compile libs: `make lib`
1. compile project: `make`

Other Make tasks:

- clean project: `make clean`
- clean lib: `make cleanlib`

Tip: A `settings.sh` file can be used to specify the version of Coq to use:

    COQBIN=/path/to/coq/bin/

If you do this, please also put a copy of `settings.sh` under `lib/tlc/src/`.

## Reference

1. [Spores](http://infoscience.epfl.ch/record/191239)
2. [Software Foundations](http://www.cis.upenn.edu/~bcpierce/sf)
3. [Types and programming languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
4. [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/)
5. [Locally Nameless](http://www.chargueraud.org/softs/ln/)
6. [TLC](http://www.chargueraud.org/softs/tlc/)

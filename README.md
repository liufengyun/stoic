# Typed Closure

The purpose of this project is to provide a sound type system
to control effects of closures.

## Motivation

The primary concern is distributed data-parallel computation like
Spark, where sending a function over the wire is very common.

When sending a function over the wire, it's important to defend
against following closure-related hazards:

- accidental capture of non-serializable variables(including `this`)
- capturing references to mutable objects
- unwanted transitive references
- the function has no side effect or its side effect can be controlled
  (via type system)

[Spores](http://infoscience.epfl.ch/record/191239) provide a type-safe
abstraction to deal with the first three problems.

This project focuses on the last problem, namely to control side
effects of closures based on a type system.

## Project Steps

| Milestones                   |          Description             |         status      |
| ----------------------------------------------------------------|----------------------
|  Milestone 1                 |    STLC + closed functions       |
|  Milestone 2                 |    System F + closed functions   |
|  ...                         |                                  |

## Reference

- [Spores](http://infoscience.epfl.ch/record/191239)

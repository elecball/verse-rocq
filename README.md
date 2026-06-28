# verse-rocq

Rocq formalization of the Verse Calculus (Augustsson et al., ICFP 2023).

## Reference

Lennart Augustsson, Joachim Breitner, Koen Claessen, Ranjit Jhala, Simon Peyton Jones,
Olin Shivers, Guy L. Steele Jr., Tim Sweeney.
*The Verse Calculus: A Core Calculus for Deterministic Functional Logic Programming.*
Proc. ACM Program. Lang., Vol. 7, ICFP, Article 203 (2023).
https://doi.org/10.1145/3607845

## Structure

```
theories/
  Syntax.v   -- syntax (expr, val, hnf, eqn), free variables, Fig. 1
  Context.v  -- contexts and context filling, Fig. 4
  Rewrite.v  -- 31 rewrite rules (all of Fig. 3)
```

## What's Implemented

- Core language syntax and semantics
- Substitution and free variable analysis
- All application, unification, elimination, normalization, and choice rules
- Context-based execution model

## TODO

- Chapter 4 - end

## Build

```
make init
make
```

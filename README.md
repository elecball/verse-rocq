# verse-rocq

Rocq (Coq) formalization of the **Verse Calculus** (Augustsson et al., ICFP 2023).

## Goals

- Mechanized metatheory of VC's small-step rewrite semantics (Fig. 3)
- Confluence of the rewrite system for well-behaved terms (Theorem 4.1)
- Consistency

## Approach

Binding representation: **Locally Nameless** (de Bruijn indices for bound variables, named atoms for free logical variables).

## Reference

> Lennart Augustsson, Joachim Breitner, Koen Claessen, Ranjit Jhala, Simon Peyton Jones, Olin Shivers, Guy L. Steele Jr., Tim Sweeney.
> *The Verse Calculus: A Core Calculus for Deterministic Functional Logic Programming.*
> Proc. ACM Program. Lang., Vol. 7, ICFP, Article 203 (2023).
> https://doi.org/10.1145/3607845

## Building

```
make
```

## Structure

```
theories/
  Syntax.v       -- Expression type, open/close, locally-closed predicate
  Contexts.v     -- Execution, value, choice context predicates
  Subst.v        -- Substitution and its properties
  Step.v         -- Single-step rewrite relation (Fig. 3)
  Confluence.v   -- Confluence proof
```

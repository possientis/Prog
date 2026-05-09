# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build

```bash
make <target>.vo        # compile a single file (e.g. make Class/Ordinal/Core.vo)
make -j$(nproc)         # compile everything in parallel
./test.sh               # full build then clean (CI equivalent)
./clean.sh              # remove all build artifacts
```

Never invoke `coqc` directly — the Makefile passes `-R . ZF` to resolve the load path and manages dependencies via `coqdep`.

All files are compiled under the logical prefix `ZF`, so `Require Import ZF.Class.Ordinal.Core` maps to `Class/Ordinal/Core.v`.

## Architecture

The project is a Coq formalization of ZF set theory, loosely following Takeuti & Zaring (1981). There are four top-level directories:

### `Axiom/`
The axiomatic foundation. `Set/Core.v` declares the universe type `U` and the membership predicate `Elem` (notation `x :< y`). The remaining files assert the ZF axioms and classical logic (`Axiom/Classic.v` — double negation, LEM).

### `Notation/`
Typeclass-based overloaded notation. Each file declares a Coq typeclass (e.g. `Slash`, `Dot`) and a notation (e.g. `://:`, `:.:`) that can be instantiated by both Class and Set types. Precedence levels matter — see memory for `:\:` (level 59), `:/\:` (60), `:\/:` (65).

### `Class/`
Theorems about **classes** — predicates `U -> Prop`. Classes are not sets in general; a class `A : Class` (where `Class := U -> Prop`) represents an arbitrary collection. Key subdirectories:

- `Class/Order/` — order-theoretic predicates: founded, well-founded, total, well-ordering, isomorphism, transitive closure, etc.
- `Class/Ordinal/` — ordinal class theory: `Ordinal`, `On` (class of all set-ordinals), arithmetic (`Plus`, `Mult`, `Exp`), recursion, fixed points.
- `Class/Relation/` — class relations as predicates on pairs: functions, bijections, domain/range, image, composition.
- `Class/Cardinal/` — cardinal class theory including Hartogs.

### `Set/`
Theorems about **sets** — elements of `U`. These mirror the `Class/` structure but work with `toClass : U -> Class` to lift sets to classes when needed. Key subdirectories parallel `Class/`: `Set/Order/`, `Set/Ordinal/`, `Set/Relation/`, `Set/Cardinal/`.

Many `Set/` proofs are direct duplicates of their `Class/` counterparts, written out in full for readability rather than derived via `toClass`. There is some `ToClass` machinery for lifting properties between the two levels, but it is not the dominant pattern.

## Proof and comment conventions

Every proof written by Claude must begin with `(* Proof by Claude. *)`.

Place a one-line informal statement of the proposition on the line **immediately above** the `Proposition`/`Lemma` keyword, at top-level indent, with the closing `*)` at column 81 (vim 1-indexed):

```coq
(* Every ordinal is transitive.                                                 *)
Proposition ...
```

All `*)` comment closers must have their `*` at **column 81** (vim 1-indexed, i.e. the 81st character). Use `./clean.sh && git diff` to verify alignment after edits.

Comments must be readable by a mathematician unfamiliar with Coq — no references to tactics, lemma names, or Coq API. Describe the mathematical content, not the proof mechanism.

Always give an informal proof sketch first, then embed it as comments inside the formal Coq proof. Interleave the informal comments with the formal tactics so each comment sits close to the formal step it describes — avoid large blobs of comments separated from the code they explain.

### Proof style preferences

- `assert (P) as H. { ... }` over `pose proof` or deep destructuring.
- `apply`/`eapply` + `assumption`/`eassumption` over `exact (Lemma a b c)`. Explicit arguments to lemmas (e.g. `apply (Succ.NotZero n)`) are fine; avoid passing local hypotheses as explicit arguments (e.g. avoid `exact (H a b)` or `rewrite (IH p H1 H2)`).
- `split. 1: reflexivity.` (goal selector) for trivial sub-goals rather than bullet blocks.
- `tac; try assumption` when a tactic leaves 2+ assumption sub-goals; `tac. N: assumption.` for exactly one.
- Hypothesis names: use sequential `H1, H2, G1, G2, K1, K2, ...` — not descriptive names like `Hfaneb` or `Gincl`; the informal comments carry the meaning.

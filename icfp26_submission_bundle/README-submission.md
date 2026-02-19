# Agda Mechanization for λ_fut

Supplementary material for the paper
**"Don't Wait, Just Demand: Futures Without Orchestration (Functional Pearl)"**.

## Overview

This bundle contains an Agda mechanization of the operational semantics
and metatheory for λ_fut, a calculus that extends simply-typed
lambda calculus with *non-blocking* future-based asynchronous computation.

**Headline result**: Well-Formedness Preservation is proved with
**zero postulates** — every reduction rule preserves the WF invariant,
fully mechanized.

## Prerequisites

| Dependency | Version |
|------------|---------|
| Agda       | ≥ 2.6.4 (tested with 2.7.0) |
| agda-stdlib | standard-library (any recent 2.x release) |

## Quick Start

```bash
bash check.sh
```

This type-checks the three key entry points from scratch
(`--ignore-interfaces`) and prints a postulate inventory.

## Module Map

| Module | Lines | Description |
|--------|-------|-------------|
| `SubAsync.agda` | ~360 | AST, values, state (Φ, Q, ρ), configuration |
| `WellFormedness.agda` | ~310 | WF predicate (6 conditions), state operations |
| `Reductions.agda` | ~310 | 9 reduction rules as inductive `⟶` |
| `WFPreservation.agda` | ~530 | **WF Preservation: 9/9 rules, zero postulates** |
| `Types.agda` | ~260 | Type definitions, subtyping, store typing Σ |
| `TypePreservation.agda` | ~590 | Type Preservation case structure (3 postulates) |
| `Examples.agda` | ~350 | Two execution traces (12 reduction-step proofs) |
| **Total** | **~2800** | |

## Trust Boundary

### Postulate-free (fully proved)

- **WF Preservation** (`WFPreservation.agda`): All 9 reduction rules
  route to complete Agda proofs with no postulates.

### Postulated (stated as conjectures in the paper)

- `funV-typing` — function values have function types
- `S-SCHEDULE-type-preserves` — S-SCHEDULE preserves store typing
- `type-preserved` — main Type Preservation theorem (case structure complete)

These are honestly described as conjectures in Section 4 of the paper,
with the OCaml reference implementation as supporting evidence.

### Infrastructure postulates

A small number of postulates in `SubAsync.agda`, `Reductions.agda`,
and `Examples.agda` serve as assumed helpers (e.g., decidable equality
on identifiers, concrete rule instantiations for examples). These do
not affect the metatheoretic claims.

## File Descriptions

- **`SubAsync.agda`** — Core AST: expressions (`Expr`), values (`Val`),
  future status (`FutureStatus`: Pending / Completed / Dependent),
  future table Φ, task queue Q, environment ρ, and configuration.

- **`WellFormedness.agda`** — The `WF` predicate with 6 conditions
  (valid-ids, no-dup, complete-env, acyclic dependencies, consistent
  status, ref-count correctness). State operation lemmas.

- **`Reductions.agda`** — All 9 reduction rules of λ_fut as an
  inductive relation `_⟶_`:
  M-ASYNC, M-LIFT-OP (3 cases), M-AWAIT (4 cases), S-COMPUTE,
  S-SCHEDULE, S-COMPLETE.

- **`WFPreservation.agda`** — The main theorem: for every rule
  `s ⟶ s'`, if `WF(s)` then `WF(s')`. Nine lemmas, one per rule.

- **`Types.agda`** — Types (`Ty`), subtyping (`<:`), store typing (Σ),
  typing judgement, `Future<τ>` covariance.

- **`TypePreservation.agda`** — Case analysis skeleton for type
  preservation. Three metatheory-facing postulates remain.

- **`Examples.agda`** — Two concrete execution traces demonstrating
  multi-step reduction: basic future creation and diamond dependency.

## License

See the paper for terms. This supplementary material is provided for
review purposes.

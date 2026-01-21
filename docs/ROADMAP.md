# Sub_Async: Research Roadmap

## Current Status

### ✅ Phase 1: OCaml Implementation (Completed)

**Deliverables:**
- `src/sub_async/` — Complete implementation
  - `syntax.ml` — AST with `Async`, `Future`, `TFuture`
  - `eval.ml` — CPS evaluator with operator polymorphism
  - `future.ml` — State machine (Pending/Completed/Dependent)
  - `scheduler.ml` — Non-deterministic task queue
  - `type_check.ml` — Type system with `future<T>` support

**Key Design Decisions:**
- Operator polymorphism: `+` detects Future types
- Implicit coordination: No explicit `await`
- Static dependency graphs: Built at operator application time

**Documentation:**
- `docs/DESIGN_DECISIONS.md` — Trade-offs
- `docs/SLIDES_SHORT.md` — Presentation slides

---

## 🚧 Phase 2: Operational Semantics Design (In Progress)

### Goal
Design small-step operational semantics and type system for Sub_Async, suitable for formal verification in Agda.

### Learning Tasks

#### Task 2.1: Analyze Aeff Implementation
**Source:** `external_resources/aeff/implementation/`

**Focus Areas:**
- [ ] `src/syntax.ml` — How do they define operations and handlers?
- [ ] `src/eval.ml` — How do they implement effect interpretation?
- [ ] `src/infer.ml` — How do they type operations and handlers?

**Questions to Answer:**
1. How does Aeff represent "async" as an effect?
2. How does their handler mechanism compare to our scheduler?
3. How do they handle effect polymorphism in types?

#### Task 2.2: Analyze Aeff Formalization
**Source:** `external_resources/aeff/formalization/`

**Focus Areas:**
- [ ] `Syntax.agda` — Inductive definitions for syntax
- [ ] `Semantics.agda` — Small-step rules
- [ ] `TypeSystem.agda` — Typing judgments
- [ ] `Soundness.agda` — Progress + Preservation proofs

**Questions to Answer:**
1. How do they define the configuration (state)?
2. How do they handle non-determinism in the semantics?
3. What invariants do they maintain for type safety?

#### Task 2.3: Study the Paper
**Source:** `external_resources/async-effects-paper/`

**Key Sections:**
- [ ] `basic-calculus-computations.tex` — Core calculus rules
- [ ] `basic-calculus-processes.tex` — Process semantics
- [ ] `aeff.tex` — Full language specification

---

### Comparative Analysis

#### Aeff vs Sub_Async: Conceptual Mapping

| Aeff Concept | Sub_Async Equivalent | Notes |
|--------------|----------------------|-------|
| Operation call | `async e` | Both "throw" computation elsewhere |
| Handler | Scheduler + Future resolution | Aeff is explicit, we're implicit |
| Effect row | `future<T>` type | Aeff is more general (multiple effects) |
| Continuation | `continuation list` in status | Both use CPS internally |
| Runner | `Scheduler.run_all` | Both execute until completion |

#### Key Differences

**1. Coordination Model**
- **Aeff:** Explicit handlers — programmer writes `handle ... with ...`
- **Sub_Async:** Implicit coordination — operators detect Futures

**2. Effect Scope**
- **Aeff:** Multiple effects, effect polymorphism
- **Sub_Async:** Single effect (async), simpler type system

**3. Dependency Tracking**
- **Aeff:** Dynamic (handler can inspect continuation)
- **Sub_Async:** Static (dependency graph built at operator time)

**4. Semantics Style**
- **Aeff:** Big-step with handlers, small-step for processes
- **Sub_Async:** Need to decide — likely small-step for all

---

### Design Decisions to Make

#### D1: Configuration Structure
```
⟨e, ρ, Σ, Q⟩
```
- `e` — Current expression
- `ρ` — Environment
- `Σ` — Future table (id → status)
- `Q` — Task queue

**Open Question:** Should we separate "main thread" from "background tasks"?

#### D2: Small-Step Rules

**Async Creation:**
```
⟨async e, ρ, Σ, Q⟩ → ⟨n, ρ, Σ[n ↦ Pending(e,ρ)], Q ∪ {n}⟩
```

**Operator Lift:**
```
⟨n₁ + n₂, ρ, Σ, Q⟩ → ⟨m, ρ, Σ[m ↦ Dependent([n₁,n₂], (+))], Q⟩
  where Σ(n₁) ≠ Completed ∨ Σ(n₂) ≠ Completed
```

**Scheduler Step (non-deterministic):**
```
⟨v, ρ, Σ, Q⟩ →_sched ⟨v, ρ, Σ', Q'⟩
  where some task in Q takes a step
```

**Open Question:** How to formalize non-determinism? LTS labels?

#### D3: Type System

**Typing Async:**
```
Γ ⊢ e : T
─────────────────
Γ ⊢ async e : future<T>
```

**Typing Operator Lift:**
```
Γ ⊢ e₁ : future<int>    Γ ⊢ e₂ : future<int>
──────────────────────────────────────────────
Γ ⊢ e₁ + e₂ : future<int>
```

**Open Question:** Subtyping? `int <: future<int>`?

---

## Phase 3: Agda Formalization (Planned)

### Directory Structure
```
formalization/
├── agda/
│   ├── Syntax.agda
│   ├── Semantics.agda
│   ├── TypeSystem.agda
│   ├── Progress.agda
│   └── Preservation.agda
└── README.md
```

### Verification Goals
1. **Progress:** Well-typed programs don't get stuck
2. **Preservation:** Types are preserved by reduction
3. **Future Safety:** All Dependent Futures eventually resolve (under fair scheduling)

---

## Timeline (Tentative)

| Week | Task |
|------|------|
| Week 1-2 | Analyze Aeff implementation + paper |
| Week 3 | Draft small-step rules on paper |
| Week 4 | Review with supervisor |
| Week 5-6 | Start Agda formalization |
| Week 7-8 | Prove Progress + Preservation |

---

## Notes & Questions for Supervisor

1. **Non-determinism:** Aeff uses labeled transitions. Should we do the same?
2. **Scope:** Should we formalize the full language or a core calculus?
3. **Short-circuit:** Should we resolve the boolean operator issue before formalization?
4. **Reference:** Any other papers on Future/Promise semantics to read?

---

## References

### Primary
- Ahman, D. & Pretnar, M. — Aeff paper (in `external_resources/async-effects-paper/`)
- Ahman, D. — Aeff Agda formalization (in `external_resources/aeff/formalization/`)

### Background
- Pierce, B. — Types and Programming Languages (TAPL)
- Harper, R. — Practical Foundations for Programming Languages (PFPL)
- Software Foundations — PLF volume (Coq, but applicable)
- PLFA — Programming Language Foundations in Agda

### Related Work
- Scala Futures formal semantics
- Concurrent ML semantics
- Algebraic effects literature (Plotkin & Pretnar)

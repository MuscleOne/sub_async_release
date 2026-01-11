# Sub_Async

> CPS-style asynchronous computation extension for the Sub language

Based on [PL Zoo](https://github.com/andrejbauer/plzoo)'s `sub` language by Andrej Bauer.

---

## Overview

This project extends the `sub` language (eager evaluation + subtyping + records) with **continuation-based asynchronous computation**.

**Key Features**:
- `async e` syntax for creating asynchronous computations
- `Future<T>` type with covariant subtyping
- Continuation auto-call mechanism (no explicit scheduler polling)
- Non-deterministic task scheduling for concurrency simulation

---

## Project Structure

```
sub_async/
├── src/
│   ├── zoo/          # PL Zoo framework (interpreter infrastructure)
│   ├── sub/          # Original sub language (baseline)
│   └── sub_async/    # Async extension (this project)
├── examples/         # Example programs
└── README.md
```

---

## Build & Run

### Prerequisites
- OCaml 4.14+
- Dune 3.0+

### Build
```bash
dune build
```

### Run Examples
```bash
# Original sub (no async)
./_build/default/src/sub/sub.exe examples/00_sub_only.sub

# Basic async demonstration
./_build/default/src/sub_async/sub_async.exe examples/01_basic.sub

# Non-deterministic scheduling
./_build/default/src/sub_async/sub_async.exe examples/02_nondeterministic.sub

# Fire-and-forget pattern
./_build/default/src/sub_async/sub_async.exe examples/03_fire_and_forget.sub
```

---

## Core Mechanism

### `async e` Syntax

```ocaml
let x = async (2 + 3) in    (* Creates future #0, returns immediately *)
x + 10                      (* Registers continuation when using x *)
```

**Implementation** ([src/sub_async/eval.ml](src/sub_async/eval.ml#L257-L260)):
```ocaml
| Async e' ->
    let id = ContinuationStore.create e' env in
    k (Future id)
```

### ContinuationStore Module

Manages futures and their continuations ([src/sub_async/eval.ml](src/sub_async/eval.ml#L57-L126)):

```ocaml
module ContinuationStore = struct
  type status =
    | Pending of expr * environment * continuation list
    | Completed of expr

  val create : expr -> environment -> int    (* Create future, schedule task *)
  val await : int -> continuation -> unit    (* Register continuation *)
  val complete : int -> expr -> unit         (* Complete and notify waiters *)
end
```

**Workflow**:
1. `create` — Generates future ID, schedules task to `Scheduler.queue`
2. `await` — Registers continuation to `ks` list (non-blocking)
3. `complete` — Executes `List.iter (fun k -> k v) ks` when task finishes

### Type System

```
Γ ⊢ e : T
─────────────────────
Γ ⊢ async e : Future T
```

**Covariance** ([src/sub_async/type_check.ml](src/sub_async/type_check.ml#L99-L101)):
```ocaml
| TFuture ty1', TFuture ty2' ->
    subtype ty1' ty2'  (* T1 <: T2 ⇒ Future T1 <: Future T2 *)
```

---

## Design Philosophy

### Space Decoupling
`async e` does not specify who executes the task — it enters a global queue.

### Time Decoupling  
`create` returns future ID immediately; task executes asynchronously. When the task completes, `complete` function calls all registered continuations.

### Key Condition
- `ks = []` (no waiters) → `complete` does nothing (fire-and-forget)
- `ks ≠ []` (has waiters) → `complete` calls all continuations

---

## Examples

| File | Purpose |
|------|---------|
| `00_sub_only.sub` | Original sub language (baseline, no async) |
| `01_basic.sub` | Basic async + continuation auto-call |
| `02_nondeterministic.sub` | Non-deterministic scheduling (run multiple times) |
| `03_fire_and_forget.sub` | Async without using result (`ks = []`) |

### 01_basic.sub
Basic demonstration of continuation auto-call:
```ocaml
let x = async (2 + 3) in
let y = async (10 * 10) in  
let z = async (7 * 8) in
x + y + z
(* Result: 161 *)
```

### 02_nondeterministic.sub
Non-deterministic scheduling — run multiple times to observe different execution orders.

### 03_fire_and_forget.sub
Creates async tasks without using results — no continuations called.

---

## Comparison with Original `sub`

| Feature | sub | sub_async |
|---------|-----|-----------|
| Evaluation | Eager | Eager + CPS |
| Async | ❌ | ✅ `async e` |
| Future type | ❌ | ✅ `Future<T>` |
| Core eval.ml | ~150 lines | ~286 lines |

**New keyword**: `async` (defined in [lexer.mll](src/sub_async/lexer.mll#L14) and [parser.mly](src/sub_async/parser.mly#L14))

---

## Acknowledgments

- **PL Zoo** by Andrej Bauer — Framework and original `sub` language
- **Supervisor's idea** — Space/time decoupling for asynchronous computation

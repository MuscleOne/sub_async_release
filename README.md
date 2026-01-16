# Sub_Async

> CPS-based async computation extension for Sub language

Extended from [PL Zoo](https://github.com/andrejbauer/plzoo)'s `sub` language by Andrej Bauer.

---

## Overview

Sub_Async extends the `sub` language (eager evaluation + subtyping + records) with **continuation-based asynchronous computation** and **Future computation graph**.

**Core Features**:
- `async e` syntax: Create non-blocking async computations
- `Future<T>` type: Covariant subtyping support
- **Automatic dependency tracking**: Operators on Futures create dependent Futures (no blocking await)
- **Auto-resolution**: Cascading Future resolution when dependencies complete
- Non-deterministic scheduling: Simulates concurrent execution

---

## Quick Start

### Prerequisites
- OCaml 4.14+
- Dune 3.0+
- Menhir 2.1+

### Ubuntu/Debian Setup

```bash
# Install opam
sudo apt update && sudo apt install -y opam

# Initialize opam
opam init -y --disable-sandboxing
eval $(opam env)

# Install build tools
opam install -y dune menhir

# Add to ~/.bashrc for persistence
echo 'eval $(opam env)' >> ~/.bashrc
```

### Build & Run

```bash
# Build
dune build

# Run examples
dune exec src/sub_async/sub_async.exe examples/01_basic.sub
```

---

## Key Feature: Future Computation Graph

### The Problem (v1.0)

```ocaml
let x = async (2+3) in
let y = async (10*10) in
x + y  (* ❌ Blocks: awaits x, then y, returns result *)
```

**Issue**: Even with `async`, operators immediately await, preventing parallelism.

### The Solution (v2.0)

```ocaml
let x = async (2+3) in        (* Future 0 *)
let y = async (10*10) in      (* Future 1 *)
x + y                         (* ✅ Returns Future 2: depends on [0, 1] *)
```

**Key Innovation**: Operators (`+`, `-`, `*`, `/`, `=`, `<`) detect Futures and create **Dependent Futures** instead of blocking.

### How It Works

```ocaml
type status =
  | Pending of expr * environment * continuation list
  | Completed of expr
  | Dependent of dependency  (* NEW in v2.0 *)

type dependency = {
  depends_on: int list;              (* Dependencies *)
  compute: expr list -> expr;        (* Combiner function *)
  waiters: continuation list;        (* Waiting continuations *)
}
```

**When `x + y` executes**:
1. Both `x` and `y` are Futures? → Create Dependent Future
2. Register dependencies: `[id_x; id_y]`
3. Return immediately (non-blocking!)
4. When dependencies complete → Auto-resolve via `check_and_resolve_dependent`

---

## Examples

| File | Purpose | Key Feature |
|------|---------|-------------|
| `00_sub_only.sub` | Baseline (original sub, no async) | Comparison |
| `01_basic.sub` | Basic async + continuation auto-call | Introduction |
| `03_fire_and_forget.sub` | Unused async tasks | Fire-and-forget |
| `04_future_graph.sub` | **Core demo**: Non-blocking operators | v2.0 showcase |
| `10_fibonacci.sub` | Fibonacci dataflow | Chain dependencies |
| `11_diamond_dependency.sub` | Diamond pattern (Fork-Join) | Parallel convergence |
| `12_mapreduce.sub` | MapReduce pattern | Map-Reduce aggregation |
| `13_pipeline.sub` | Pipeline pattern | Cascading stages |

### Core Demo: Non-blocking Operators

**File**: `examples/04_future_graph.sub`

```ocaml
let x = async (2 + 3) in       # Future 0
let y = async (10 * 10) in     # Future 1
let z = async (7 * 8) in       # Future 2
let sum = x + y + z in         # Future 3,4 (returns immediately!)
3 + 1                          # Returns 4 without waiting!
```

**Output**:
```
[dependent] Future #3 depends on [0; 1]
[dependent] Future #4 depends on [3; 2]
[main] Final result obtained        ← Before futures complete!
- : int = 4                         ← Result of 3+1
```

**Proof**: `3 + 1` executes before async tasks finish — true non-blocking behavior!

---

## Classic Concurrency Patterns

Our space/time decoupling design naturally supports classic algorithms:

### 🔷 Diamond (Fork-Join)

```
      fetch_user
       /      \
  validate  check_quota  ← Parallel (space decoupling)
       \      /
    create_order         ← Auto-wait (time decoupling)
```

**Example**: `examples/11_diamond_dependency.sub`

### 🗺️ MapReduce

```
map1  map2  map3  map4   ← Parallel tasks
   \    |    |   /
      reduce           ← Auto-aggregation
```

**Example**: `examples/12_mapreduce.sub` (verified random scheduling across 5 runs)

### 🌊 Pipeline

```
fetch → transform → validate → save  ← Auto-cascade
```

**Example**: `examples/13_pipeline.sub`

### 🔢 Fibonacci Dataflow

Chain dependencies with automatic cascade resolution.

**Example**: `examples/10_fibonacci.sub`

---

## Design Philosophy

### Space Decoupling
`async e` doesn't specify **who** executes the task — enters global queue, scheduler picks randomly.

### Time Decoupling
`async` returns immediately; task executes asynchronously. On completion, registered continuations are called automatically.

### DAG by Design
Future computation graph is a **DAG (Directed Acyclic Graph)** by construction:
- Let bindings enforce ordering (no forward references)
- Static scoping prevents cycles
- Immutable Futures cannot be modified after creation

**Result**: Cycles are theoretically impossible — no cycle detection needed in practice (though implemented defensively).

---

## Implementation Highlights

- **Scheduler**: Non-deterministic (random task selection from ready queue)
- **ContinuationStore**: Manages Future states and automatic notifications
- **Dependent Future resolution**: `check_and_resolve_dependent` triggers cascading resolution
- **Type system**: Covariant `Future<T>` subtyping

**Core code**: ~286 lines (vs ~150 for original sub)

---

## Comparison with Original Sub

| Feature | sub | sub_async |
|---------|-----|-----------|
| Evaluation | Eager | Eager + CPS |
| Async support | None | `async e` |
| Future type | None | `Future<T>` |
| Dependency tracking | None | Automatic |

---

## Acknowledgments

- **PL Zoo** by Andrej Bauer — Framework and original `sub` language
- **Supervisor's guidance** — Space/time decoupling design inspiration

---
title: "The Introduction of Sub_Async Language"
subtitle: "Toward Implicit Parallelism via Operator Polymorphism"
author: "Chen Tianhao"
date: "January 2026"
classoption: "aspectratio=169"
theme: "metropolis"
---

## Outline

1. **Three Problems**
   - Who executes? → Space decoupling
   - When to wait? → Time decoupling
   - How to coordinate? → Operator polymorphism

2. **Case Study: Diamond**
   - Step-by-step trace

3. **More Examples**
   - Fire-and-Forget
   - Parallel Fibonacci

4. **Trade-offs & Open Problems**

---

## Problem 1: OOP Invocation

**Every method call requires a receiver:**

```python
executor.submit(task)      # Which executor?
thread_pool.run(job)       # Which thread pool?
```

**The burden:** You must always specify *who* does the work.

---

## The Chat Group Analogy

```
[You]: "I need someone to calculate the report"
       (posts to group, doesn't care who picks it up)

[Alice]: (sees it, starts working)
[Alice]: "Done! Here's the result."
```

**You didn't specify who.** You just threw it out there.

---

## Space Decoupling

**Instead of:**
```python
executor.submit(expensive_computation)
```

**What if:**
```ocaml
async (expensive_computation)   (* Just throw it out *)
```

The request enters a global pool. Someone picks it up.

---

## Problem 2: Blocking

**Traditional evaluation is sequential:**

```ocaml
let x = expensive_1()     (* Block. Wait. *)
let y = expensive_2()     (* Block. Wait. *)
x + y                     (* Finally! *)
```

---

## Time Decoupling

**Throw out requests, pretend they're done:**

```ocaml
let x = async (expensive_1())   (* Returns immediately *)
let y = async (expensive_2())   (* Returns immediately *)
x + y                            (* Now we need results *)
```

**Return Future, demand result later.**

---

## Problem 3: Await Destroys Parallelism

```javascript
let x = await async(f())    // Sequential!
let y = await async(g())    // Must wait for x
x + y
```

```javascript
let [x, y] = await Promise.all([   // Manual!
  async(f()), async(g())
])
```

**Can the compiler find parallelism automatically?**

---

## The Insight

**What if `+` could detect Futures?**

```ocaml
x + y   where x, y : int           →  compute now
x + y   where x, y : Future<int>   →  ???
```

---

## The Answer

**Don't wait. Build dependency graph instead.**

```ocaml
x + y   where x, y : Future<int>
    ↓
Future { depends_on: [x, y], compute: (+) }
```

Return immediately. Resolve when dependencies complete.

---

## The Result

```ocaml
let x = async (f())   (* Future #0, scheduled *)
let y = async (g())   (* Future #1, scheduled *)
x + y                  (* Future #2, depends on [#0, #1] *)
```

**No await. No Promise.all. Parallelism emerges.**

---

## The State Machine

```ocaml
type status =
  | Pending of expr * env * continuation list
  | Completed of value
  | Dependent of { depends_on: int list; 
                   compute: value list -> value }
```

- `async` creates **Pending** (scheduled computation)
- Operators create **Dependent** (waiting for inputs)

---

## Operator Polymorphism

```ocaml
let binary_op op v1 v2 k = match v1, v2 with
  | Future id1, Future id2 ->
      let id = create_dependent [id1; id2] 
        (fun [a;b] -> op a b) in
      k (Future id)
  | Future id, Int n | Int n, Future id ->
      let id = create_dependent [id] 
        (fun [a] -> op a n) in
      k (Future id)
  | Int a, Int b -> 
      k (Int (op a b))
```

**Type dispatch:** Same syntax, different semantics.

---

## Case Study: Diamond

```ocaml
let base = async (100) in
let left = base + 10 in
let right = base + 20 in
left + right
```

**Goal:** Trace how dependency graph builds itself.

---

## Step 1: async (100)

```ocaml
let base = async (100) in ...
```

- `Future.create (100)` → ID #0
- `table[#0] = Pending(100, env, [])`
- Task scheduled to evaluate `100`

**Returns:** `Future #0` (immediately, non-blocking)

---

## Step 2: base + 10

```ocaml
let left = base + 10 in ...
```

- Evaluate `base` → `Future #0`
- Evaluate `10` → `Int 10`
- `binary_op` sees `(Future #0, Int 10)`
- `create_dependent [#0] (fun [v] -> v+10)` → ID #1

**Returns:** `Future #1` (depends on #0)

---

## Step 3: base + 20

```ocaml
let right = base + 20 in ...
```

- Same pattern as Step 2
- `create_dependent [#0] (fun [v] -> v+20)` → ID #2

**Returns:** `Future #2` (also depends on #0)

---

## Step 4: left + right

```ocaml
left + right
```

- `binary_op` sees `(Future #1, Future #2)`
- `create_dependent [#1, #2] (fun [a,b] -> a+b)` → ID #3

**Returns:** `Future #3` (depends on #1 and #2)

---

## The Dependency Graph

```
       #0           ← Pending (only real computation)
      /  \
    #1    #2        ← Dependent (waiting)
      \  /
       #3           ← Dependent (waiting)
```

**4 Futures. Only 1 scheduled task. Fork-join emerges.**

---

## Resolution Cascade

```
Scheduler runs #0 → completes with 100
  → #1: deps=[#0] all done → compute 100+10=110
  → #2: deps=[#0] all done → compute 100+20=120
  → #3: deps=[#1,#2] all done → compute 110+120=230

Final: 230
```

**Automatic propagation. No manual coordination.**

---

## More Examples: Fire-and-Forget

```ocaml
let x = async (2 + 3) in
let y = async (10 * 10) in
let sum = x + y in       (* Dependent Future, returns immediately *)
3 + 1                    (* Executes now! Returns 4 *)
```

**Key:** `sum` is created but never awaited. Program returns `4`.

---

## Fire-and-Forget: Dependency Graph

```
  #0 (async 2+3)    #1 (async 10*10)
        \              /
         \            /
          #2 (x + y)     ← Created, never awaited
          
Program returns: 3 + 1 = 4   ← Immediate!
```

**Futures run in background. Main thread doesn't wait.**

---

## More Examples: Parallel Fibonacci

```ocaml
fun fib(n : int) : future int is
  if n < 2 then async (n)
  else
    let left = fib (n - 1) in    (* future int *)
    let right = fib (n - 2) in   (* future int *)
    left + right                  (* Dependent Future *)
```

**Tree parallelism:** `fib(6)` creates 25 Futures automatically.

---

## Parallel Fibonacci: Dependency Graph

```
                    fib(4)
                   /      \
              fib(3)      fib(2)
             /     \      /    \
         fib(2)  fib(1) fib(1) fib(0)
         /    \
     fib(1) fib(0)
```

**Each node = Future. Leaves = Pending. Internal = Dependent.**

---

## The Trade-off

**We support (static dependencies):**

```ocaml
let x = async f() in
let y = async g() in
x + y
```

**We don't support (dynamic dependencies):**

```ocaml
let x = async f() in
let y = async (g (await x)) in   (* y depends on x's VALUE *)
x + y
```

**Monads can. We chose simplicity.**

---

## Open Problem: Short-Circuit

```ocaml
false && x   →   false   (* Don't evaluate x *)
```

**But:**

```ocaml
let x = async (expensive()) in
false && x   (* x already scheduled! *)
```

**Conflict:** Short-circuit needs lazy. Futures are eager.

Current solution: Boolean ops don't lift to `Future<bool>`.

---

## Summary

| Design Choice | Trade-off |
|---------------|-----------|
| Operator polymorphism | Implicit parallelism, but limited to static deps |
| No explicit await | Clean syntax, but can't express dynamic deps |
| Eager scheduling | Max parallelism, but conflicts with short-circuit |

**Philosophy:** Let the compiler manage coordination.

---

## Questions?

**Code:** `github.com/MuscleOne/sub_async_release`

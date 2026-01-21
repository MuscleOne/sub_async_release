---
title: "Dependent Futures: Implicit Parallelism through Operator Polymorphism"
subtitle: "A Design Philosophy for Async Computation"
author: "Sub_Async Project"
date: "January 2026"
---

# Presentation Outline

::::: {.columns}
:::: {.column width="50%"}

1. **Motivation**
   - The problem with OOP invocation
   - The problem with blocking evaluation

2. **Two Decouplings**
   - Space decoupling: "Who does the work?"
   - Time decoupling: "When is the result needed?"

3. **The Key Insight**
   - Operators detect Futures
   - Build dependency graphs implicitly

::::
:::: {.column width="50%"}

4. **Dependent Futures**
   - The state machine
   - Dependency resolution

5. **Case Studies**
   - Diamond dependency
   - Recursive Fibonacci

6. **Limitations & Open Questions**

::::
:::::

::: notes
20-minute talk. Focus on design philosophy, not formal semantics.
Use concrete examples throughout.
:::

---

# Part 1: Motivation

**The Problem:** Traditional programming forces us to specify too much

&nbsp;

**This Part:**

- A familiar pattern: method invocation in OOP
- A familiar pain: blocking evaluation
- The question: Can we do better?

---

# The OOP Invocation Pattern

**Every method call requires a receiver:**

```python
executor.submit(task)      # Must specify: which executor?
thread_pool.run(job)       # Must specify: which thread pool?
database.query(sql)        # Must specify: which database?
```

&nbsp;

**The pattern:** `receiver.method(args)`

**The burden:** You must always know *who* does the work.

::: notes
This is so familiar we don't question it.
But do we really need to specify the executor every time?
:::

---

# A Chat Group Analogy

**Consider a WeChat/Slack group:**

```
[You]: "I need someone to calculate the quarterly report"
[You]: (posts request to group, doesn't care who picks it up)

[Alice]: (sees the request, starts working)
[Bob]:   (also available, but Alice was faster)

[Alice]: "Done! Here's the result."
```

&nbsp;

**Observation:** You didn't specify *who* should do it.

You just... threw the request out there.

---

# What If Programming Worked Like This?

**Instead of:**

```python
executor.submit(expensive_computation)   # Must specify executor
```

**What if we could write:**

```ocaml
async (expensive_computation)   (* Just "throw it out there" *)
```

&nbsp;

**The request enters a global pool.**

**Someone picks it up. We don't care who.**

::: notes
This is the first insight: decouple the task from who executes it.
:::

---

# The Second Problem: Blocking

**Traditional evaluation is sequential:**

```ocaml
let x = expensive_1()     (* Block. Wait. *)
let y = expensive_2()     (* Block. Wait. *)
let z = expensive_3()     (* Block. Wait. *)
x + y + z                 (* Finally! *)
```

&nbsp;

**The chain:** $M_1 \to M_2 \to M_3 \to \cdots$

**Each arrow is a blocking wait.**

---

# What We Actually Want

**Throw out requests, pretend they're done:**

```ocaml
let x = async (expensive_1())   (* Returns immediately! *)
let y = async (expensive_2())   (* Returns immediately! *)
let z = async (expensive_3())   (* Returns immediately! *)
(* ... do other things ... *)
x + y + z                       (* Now we need the results *)
```

&nbsp;

**The "someone else" becomes a continuation.**

**They compute in the background, wait with the result.**

**When we need it, we call for it.**

---

# Two Decouplings

::::: {.columns}
:::: {.column width="50%"}

**Space Decoupling**

- Don't specify *who* executes
- Task enters global queue
- Scheduler decides

::::
:::: {.column width="50%"}

**Time Decoupling**

- Don't block waiting for result
- Return immediately with Future
- Demand result when needed

::::
:::::

&nbsp;

**The question:** How do we compose these decoupled computations?

---

# Part 2: The Core Insight

**Goal:** Compose async computations without explicit coordination

&nbsp;

**This Part:**

- The problem with `await`
- The key insight: operators can detect Futures
- Building dependency graphs implicitly

---

# The Problem with Await

**Traditional async/await:**

```javascript
let x = await async(expensive_1())   // ← Synchronization point!
let y = await async(expensive_2())   // ← Sequential!
x + y
```

&nbsp;

**`await` is an explicit synchronization point.**

**It destroys parallelism.**

::: notes
The moment you write `await`, you're forcing sequential execution.
:::

---

# The "Engineering Hack": Manual Parallelization

```javascript
let [x, y] = await Promise.all([
  async(expensive_1()),
  async(expensive_2())
])
x + y
```

&nbsp;

**Problems:**

- Programmer must manually identify parallel opportunities
- Not composable (what if `expensive_2` depends on `expensive_1`?)
- Error-prone

---

# This Isn't Elegant!

&nbsp;

&nbsp;

**We want the compiler to find parallel opportunities.**

**We want to write simple code and get parallelism for free.**

&nbsp;

*Can we do something more principled?*

---

# The Key Insight (1/3)

**What if operators could *detect* their operands' types?**

```ocaml
x + y   where x : int, y : int
  ↓
compute immediately: x + y
```

&nbsp;

**Normal case:** Both operands are values. Compute now.

---

# The Key Insight (2/3)

**What if operators could *detect* their operands' types?**

```ocaml
x + y   where x : Future<int>, y : Future<int>
  ↓
???
```

&nbsp;

**New case:** Operands are Futures. What should happen?

::: notes
Pause here. Let the audience think.
:::

---

# The Key Insight (3/3)

**Don't wait. Register dependency instead!**

```ocaml
x + y   where x : Future<int>, y : Future<int>
  |
Future #2 { 
  depends_on: [x, y], 
  compute: fun [v1, v2] -> v1 + v2 
}
```

&nbsp;

**Return immediately with a new Future.**

**The dependency graph builds itself!**

---

# No Explicit Coordination

```ocaml
let x = async (expensive_1())     (* Future #0 *)
let y = async (expensive_2())     (* Future #1 *)
x + y                              (* Future #2: depends on [#0, #1] *)
```

&nbsp;

**No `await`.** No `Promise.all`.** No manual coordination.**

The `+` operator does the work for us.

---

# Part 3: Dependent Futures

**Goal:** Formalize the design

&nbsp;

**This Part:**

- The state machine: Pending, Completed, Dependent
- How dependencies resolve
- The computation graph

---

# The State Machine

```ocaml
type status =
  | Pending of expr * env * continuation list
  | Completed of value * dependency_list
  | Dependent of dependency

type dependency = {
  depends_on: int list;           (* Which Futures we wait for *)
  compute: value list -> value;   (* How to combine results *)
  waiters: continuation list;     (* Who's waiting for us *)
}
```

&nbsp;

**Three states. Two sources of Futures.**

---

# Two Ways to Create a Future

**1. Async (user-initiated):**

```ocaml
async (expr)   →   Future #n (Pending)
```

Computation is scheduled. Result comes later.

&nbsp;

**2. Operator (compiler-generated):**

```ocaml
future_a + future_b   →   Future #n (Dependent)
```

No computation yet. Waiting for dependencies.

---

# Dependency Resolution

**When a Pending Future completes:**

1. Update state: `Pending → Completed`
2. For each waiter: call the continuation
3. For each Dependent Future that depends on us: check if all dependencies are done

&nbsp;

**When all dependencies of a Dependent Future complete:**

1. Compute the result: `compute([v1, v2, ...])`
2. Update state: `Dependent → Completed`
3. Notify our waiters

---

# The Cascade Effect

```
Future #0 completes
    ↓
Check: Does #2 depend on #0? Yes.
Check: Are all of #2's dependencies complete? 
    ↓
If #1 is also complete → Resolve #2
    ↓
Check: Does anything depend on #2?
    ↓
... (cascade continues)
```

&nbsp;

**Automatic propagation. No manual coordination.**

---

# Computation Graph: Diamond

```ocaml
let base = async (100) in      (* #0 *)
let left = base + 10 in        (* #1: depends on [#0] *)
let right = base + 20 in       (* #2: depends on [#0] *)
left + right                    (* #3: depends on [#1, #2] *)
```

```
         base (#0)
        /         \
   left (#1)    right (#2)
        \         /
       result (#3)
```

**Fork-join pattern emerges automatically!**

---

# Part 4: Implementation Sketch

**Goal:** Show how the code realizes the design

&nbsp;

**This Part:**

- Operator polymorphism in `eval.ml`
- State management in `future.ml`
- Scheduling in `scheduler.ml`

---

# Operator Polymorphism

```ocaml
(* eval.ml *)
let binary_int_op op v1 v2 k = 
  match v1, v2 with
  | Future id1, Future id2 ->
      (* Both Futures → Create Dependent Future *)
      let new_id = Future.create_dependent_future [id1; id2]
        (fun [v1; v2] -> Int (op (to_int v1) (to_int v2)))
      in k (Future new_id)
  
  | Future id, Int n | Int n, Future id ->
      (* Mixed → Still create dependency *)
      ...
  
  | Int n1, Int n2 ->
      (* Both values → Compute now *)
      k (Int (op n1 n2))
```

---

# The Async Primitive

```ocaml
(* eval.ml *)
| Async e' ->
    let id = Future.create e' env in   (* Create + schedule *)
    k (Future id)                       (* Return immediately *)

(* future.ml *)
let create e env =
  let id = fresh_id () in
  Hashtbl.add table id (Pending (e, env, []));
  Scheduler.schedule (fun () ->         (* Throw into queue *)
    eval_cps env e (fun v -> complete id v));
  id
```

---

# Dependency Resolution

```ocaml
(* future.ml *)
let rec check_and_resolve_dependent id =
  match Hashtbl.find table id with
  | Dependent { depends_on; compute; waiters } ->
      if all_completed depends_on then begin
        let values = List.map get_value depends_on in
        let result = compute values in
        Hashtbl.replace table id (Completed (result, depends_on));
        List.iter (fun k -> k result) waiters  (* Notify! *)
      end
  | _ -> ()
```

---

# Part 5: Case Studies

**Goal:** See the design in action

&nbsp;

**This Part:**

- Diamond dependency (fork-join)
- Recursive Fibonacci (tree parallelism)

---

# Case Study 1: Diamond

```ocaml
(* examples/11_diamond_dependency.sub *)
let base = async (100) in
let left = base + 10 in
let right = base + 20 in
left + right
```

**Execution trace:**

1. `async (100)` → Future #0 (Pending), scheduled
2. `base + 10` → Future #1 (Dependent on [#0])
3. `base + 20` → Future #2 (Dependent on [#0])
4. `left + right` → Future #3 (Dependent on [#1, #2])
5. Scheduler runs #0 → completes with 100
6. #1 and #2 resolve in parallel
7. #3 resolves → 230

---

# Case Study 2: Fibonacci

```ocaml
(* examples/10b_fibonacci_parallel.sub *)
fun fib(n : int) : future int is
  if n < 2 then 
    async (n)
  else 
    fib(n-1) + fib(n-2)    (* Recursive Futures! *)
```

**`fib(4)` creates:**

```
        fib(4)
       /      \
   fib(3)    fib(2)
   /    \
fib(2) fib(1)
```

**9 Futures total. Tree parallelism emerges automatically.**

---

# Part 6: Limitations & Open Questions

**Goal:** Honest assessment of what we haven't solved

&nbsp;

**This Part:**

- Short-circuit evaluation conflict
- Static vs dynamic dependencies
- What's next?

---

# Problem: Short-Circuit Evaluation

**Boolean operators have short-circuit semantics:**

```ocaml
false && x   →   false    (* Don't evaluate x! *)
true  || x   →   true     (* Don't evaluate x! *)
```

&nbsp;

**But Futures want parallel evaluation:**

```ocaml
let x = async (expensive()) in
false && x   (* Should x run? It's already scheduled! *)
```

**Conflict:** Short-circuit requires conditional evaluation. 

Futures require eager scheduling.

---

# Current Inconsistency

**Arithmetic operators:** Support `Future<int>`

```ocaml
Future<int> + Future<int>  ->  Future<int>   [OK]
```

**Boolean operators:** Don't support `Future<bool>`

```ocaml
Future<bool> && Future<bool>  ->  ???        [NO]
```

&nbsp;

**Comparison can produce `Future<bool>`, but boolean ops can't consume it.**

This is a design debt we haven't resolved.

---

# Static vs Dynamic Dependencies

**We support:**

```ocaml
let x = async f() in
let y = async g() in
x + y                    (* Static: structure known at compile time *)
```

**We don't support:**

```ocaml
let x = async f() in
let y = async (g(await x)) in   (* Dynamic: y depends on x's VALUE *)
x + y
```

&nbsp;

**Monads can express dynamic dependencies. We can't.**

This is a deliberate trade-off: simplicity over expressiveness.

---

# Summary: The Design Philosophy

&nbsp;

**1. Space Decoupling:** Don't specify who executes. Just "throw it out."

**2. Time Decoupling:** Don't block. Return Future, demand later.

**3. Implicit Coordination:** Operators detect Futures, build graphs automatically.

&nbsp;

**The programmer describes computation logic.**

**The system manages parallelism.**

---

# What's Next?

**Immediate:**

- Resolve the short-circuit inconsistency
- Add exception propagation (`Result<T, E>` instead of exceptions)
- Add cancellation mechanism

&nbsp;

**Future:**

- Formal operational semantics
- Type safety proof (progress + preservation)
- Real multi-threaded scheduler

---

# Thank You

&nbsp;

**Code:** `github.com/MuscleOne/sub_async_release`

**Based on:** PL Zoo by Andrej Bauer

&nbsp;

**Questions?**

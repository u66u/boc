## What it is

Proof of core semantics of behavior oriented concurrency

## How it works

The proof is deliberately split into small pieces. Each piece answers one question:

- Which mutable memory may a behavior access?
- Which behaviors may run at the same time?
- Can the cown-acquisition protocol create a deadlock?
- When can the whole machine become stuck?

### 1. Cowns own mutable regions

Every cown gets its own private slice of memory, and no two cowns share a slice. Immutable data is the one exception: since it can't change, it's safe for anyone to look at. We represent this by tagging the location with its owner. A location is therefore conceptually an owner cown + an address local to that cown. This works for both simple and realistic heaps. A cown may own one mutable cell,or it may own an entire region containing many objects. We don't really care about the region's size

### 2. Behaviors declare their claims

A behavior has:

- a unique id
- a set of cowns it claims
- its local execution state

Because the language inside a behavior is left abstract, we ask it to promise exactly three things:

- Any behavior only ever touches memory inside cowns it has actually claimed
- A step never changes anything outside the cowns it holds
- Body progress - at every point, a well-behaved behavior is either done, able to take a step, or able to spawn a child

Everything else in the proof is downstream of them.

### 3. The scheduler is a small independent kernel

The scheduler keeps two collections:

- an ordered list of pending behaviors
- a set of active behaviors

The pending collection is a list because order matters. A behavior may start only if it conflicts with neither an active behavior nor an earlier pending behavior

There are four kinds of transition:

1. **Start.** Remove an eligible behavior from the pending list and add it to the active set
2. **Execute.** Advance an active behavior's local state and possibly the heap
3. **Spawn.** Advance the parent and append a fresh child to the pending list
4. **Finish.** Remove a completed behavior from the active set

Starting makes the behavior active with its entire claim in one transition. There is no state in which the behavior owns some of its requested cowns while waiting for the rest

Spawning is asynchronous. The parent does not acquire the child's cowns anddoes not wait for the child. Finishing removes the behavior from the active set,which releases all of its claims together.

The full semantics contain heaps and body states, but the kernel doesn't. A small projection lemma shows that every full transition either performs the corresponding scheduler transition or leaves the scheduler state unchanged, and this is the only bridge needed

### 4. Scheduler safety: no two running behaviors ever share a cown

This is the load-bearing invariant. It's checked by walking through the four moves one at a time:

- Step and Spawn don't touch who's running or what they've claimed, so they trivially preserve the invariant
- Finish only removes someone from the running set — removing someone can't create a new conflict
- Start is the only interesting case, and it's protected exactly by the eligibility check: a behavior is only allowed to start if its claim doesn't overlap anyone currently running

A direct consequence is that a cown can be captured by at most one active behavior at a time, race freedom falls out immediately

### 5. Deadlock freedom

Classic deadlock needs a cycle: A holds something B wants, while B holds something A wants. That requires a state where a task can hold some resources while waiting on more. But in this model, that state doesn't exist - a behavior is either pending and holding nothing, or running and holding everything it will ever hold at once. There's no moment where a behavior is half-acquired. Remove the possibility of holding one thing while waiting for another, and you've removed the raw material a deadlock cycle would need to be built from

The only other place a `waiting` relationship could sneak in is the ordering of the pending queue itself (an earlier pending behavior blocking a later one). But queue order only ever points backward toward earlier entries - it can't loop back on itself, the same way you can't queue behind someone who is queued behind you. So that source of waiting is acyclic by construction too

### Progress and conflict guarantees

The former requires that you use exclusively cowns for concurrency, you can't spawn arbitrary threads, but BOC itself can't get stuck. The proof is just an exhaustive check of the possible states: if anything is running, body progress guarantees it can step, spawn, or finish. If nothing is running but something is pending, the first thing in the queue has nothing ahead of it and nothing running to conflict with, so it's automatically eligible to start. The only case left is nothing running and nothing pending, which is the actual terminal state

If two behaviors conflict and one appears earlier in program order, the second one can't start until the first one finishes - not while it's pending (blocked by the earlier-pending check) and not while it's running (blocked by the running-conflict check). So conflicting behaviors execute in the order they were spawned

### 6. What it does and doesn't prove

What it proves: if a host language honestly satisfies the three promises (access confinement, frame property, body progress), and the scheduler follows exactly these four rules, then the resulting system can never race and can never deadlock on cown acquisition as a matter of pure logical necessity. It also proves the system never gets stuck prematurely, and that conflicting tasks run in a predictable order.

What it doesn't prove:

- It cannot prove that a host language implement the 3 promises stated above, that's the compiler's job
- It doesn't verify any actual implementation. Real BoC runtimes acquire cowns using lock-free queues, CAS operations, and a sorted acquisition order across possibly many CPU cores at once This proof replaces all of that with a single atomic "Start" step
- It says nothing about fairness, starvation, or termination. "Not stuck" only means some transition is always available, it doesn't promise every pending task eventually gets its turn, or that computation as a whole ever finishes

Therefore, it is not suitable to be used as a verified runtime or a compiler target, although it can be a foundation to one

## Usage

In a Mathlib-enabled Lean 4 project you can check the public entry point with:

```sh
lake env lean boc.lean
```


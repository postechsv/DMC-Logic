# Tutorial: Verifying the Bakery Algorithm

This tutorial explains how to verify the safety of Lamport's Bakery Algorithm using the **DMC-Logic** framework. We will walk through encoding the system transitions, defining inductive invariants, and proving mutual exclusion.

---

## 1. Representing Rewrite Theories

In DMC-Logic, the system state is represented by a configuration `Conf`. The transitions between states are defined using an inductive proposition `Step`. 

The Bakery algorithm uses a global ticket counter (`t`) and a serving counter (`s`). Processes move through states: `idle` → `wait` → `crit`.

```lean
inductive Step : Conf → Conf → Prop where
  -- A process picks a ticket (t) and moves to wait state
  | wake : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n,      s := m, c := {$[idle]}   + ps}
           {t := succ n, s := m, c := {$[wait n]} + ps}

  -- A process enters the critical section if its ticket matches the serving counter (s)
  | crit : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n, s := m, c := {$[wait m]} + ps}
           {t := n, s := m, c := {$[crit m]} + ps}

  -- A process exits, incrementing the serving counter
  | exit : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n, s := m,      c := {$[crit m]} + ps}
           {t := n, s := succ m, c := {$[idle]} + ps}

infix:110 " ⇒ " => Step
infix:110 " ⇒* " => Relation.ReflTransGen Step

## 2. Representing Inductive Invariants
To prove safety, we define predicates that describe all "reachable" and "safe" states. We categorize the system state into three main phases:

### Initial State
The system starts with the ticket and serving counters equal, and all processes `idle`.

```lean
def init_pred (cf : Conf) : Prop :=
  cf.t = cf.s ∧ is cf.c
```

### Waiting State
When processes are waiting, their tickets must be between the current serving counter and the next available ticket.

```lean
def wait_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧ ws cf.c ∧ 
  (∀ k ∈ tickets cf.c, k ≥ cf.s ∧ k < cf.t) ∧ 
  ((tickets cf.c).Nodup)
```

### Critical State
If a process is in the critical section, it must hold the ticket exactly matching `cf.s`.

```lean
def crit_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧
  ∃ ps : ProcSet,
    cf.c = {$[crit cf.s]} + ps ∧
    ws ps ∧
    (∀ k ∈ tickets ps, k > cf.s ∧ k < cf.t) ∧ 
    ((tickets ps).Nodup)
```

### The Global Invariant
The overall invariant Inv is the disjunction of these three possibilities.

```lean
def Inv (cf : Conf) : Prop :=
  init_pred cf ∨ wait_pred cf ∨ crit_pred cf
```

## 3. Verifying Safety by Inductive Invariants
Verification in `bakery.lean` follows the standard inductive approach. We must prove two main properties:

1. base step: The starting state satisfies Inv.
2. inductive step: Every valid Step preserves Inv.

### Base Step
We prove that the initial configuration (where `t=0`, `s=0`, and all processes are `idle`) satisfies `init_pred`.

```lean
theorem inv_step : ∀ cf cf' : Conf, Inv cf → cf ⇒ cf' → Inv cf' := by
  intros cf cf' h_inv h_step
  cases h_step <;> cases h_inv
  -- The proof proceeds by analyzing how each transition 
  -- affects the ticket ranges and the Nodup property.
```

### Inductive Step
For every transition in `Step` (`wake`, `crit`, `exit`), we show that if `Inv cf` holds, then `Inv cf` must also hold.

```lean
theorem inv_step : ∀ cf cf' : Conf, Inv cf → cf ⇒ cf' → Inv cf' := by
  intros cf cf' h_inv h_step
  cases h_step <;> cases h_inv
  -- The proof proceeds by analyzing how each transition 
  -- affects the ticket ranges and the Nodup property.
```

## 4. Final Safety Result: Mutual Exclusion
The ultimate goal is to prove Mutual Exclusion: no two processes can be in the `crit` state simultaneously. Once we have proven that `Inv` is inductive, we derive the final safety theorem:

```lean
theorem safety : ∀ cf : Conf, init_conf ⇒* cf → Inv cf := by
  apply Relation.ReflTransGen.connective_property
  . apply inv_init
  . apply inv_step

-- This ensures that it is impossible for two different processes 
-- to be in the critical section at the same time.
theorem mutual_exclusion : ∀ cf : Conf, Inv cf → 
  (∀ m n, {$[crit m]} + {$[crit n]} ⊆ cf.c → m = n) := by
  -- Follows from the structure of crit_pred
```

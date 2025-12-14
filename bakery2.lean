--- temporary file for refactoring bakery.lean
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Logic.Relation
import Bakery.DMC2


inductive Mode where
  | idle
  | wait : Nat → Mode
  | crit : Nat → Mode


inductive Proc where
  | proc : Mode → Proc


notation "$[" m "]" => Proc.proc m

abbrev ProcSet := Multiset Proc

structure Conf where
  t : Nat
  s : Nat
  c : ProcSet

open Mode Proc Nat
open scoped Multiset

inductive Step : Conf → Conf → Prop where
  | wake : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n,      s := m, c := {$[idle]}   + ps}
           {t := succ n, s := m, c := {$[wait n]} + ps}
  | crit : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n, s := m, c := {$[wait m]} + ps}
           {t := n, s := m, c := {$[crit m]} + ps}
  | exit : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n, s := m,      c := {$[crit m]} + ps}
           {t := n, s := succ m, c := {$[idle]} + ps}

--- DMC: Define the System instance for Conf
instance : System Conf := ⟨Step⟩


def init1 : Conf :=
  {t := 0, s := 0, c := {$[idle]}}

--- notations (e.g., =>*) are available from DMC
example : init1 ⇒* init1 := by
  apply Relation.ReflTransGen.refl

--- all proces are idle
def is (ps : ProcSet) :=
  ∀m ∈ ps, m = $[idle]

--- all procs are either idle or waiting
def ws (ps : ProcSet) :=
  ∀m ∈ ps, (m = $[idle] ∨ ∃ n, m = $[wait n])

def Proc.ticket? : Proc → Option Nat
  | $[wait n] => some n
  | $[crit n] => some n
  | $[idle]   => none

--- return the set of all ticket numbers in a procset
def tickets (ps : ProcSet) : Multiset Nat := ps.filterMap Proc.ticket?


---------------------------
--- Inductive Invariant ---
---------------------------

def init_pred (cf : Conf) : Prop :=
  cf.t = cf.s ∧ is cf.c

--- DMC: Define the ISystem instance for Conf
instance : ISystem Conf where
  init := init_pred
  step := Step

def wait_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧ ws cf.c ∧ (∀ k ∈ tickets cf.c, k ≥ cf.s ∧ k < cf.t) ∧ ((tickets cf.c).Nodup)


def crit_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧
  ∃ ps : ProcSet,
    cf.c = {$[crit cf.s]} + ps ∧
    ws ps ∧
    (∀ k ∈ tickets ps, k > cf.s ∧ k < cf.t) ∧
    ((tickets ps).Nodup)

def inv_pred (cf : Conf) : Prop :=
  init_pred cf ∨ wait_pred cf ∨ crit_pred cf

--- DMC: Define the ISystem instance for Conf
instance : IndInv Conf inv_pred where
  base cf h0 := by sorry
  ind cf cf' h := by sorry

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

---
instance : System Conf where
  step := Step


def init1 : Conf :=
  {t := 0, s := 0, c := {$[idle]}}

--- notations (e.g., =>*) are available from DMC
example : init1 ⇒* init1 := by
  apply Relation.ReflTransGen.refl

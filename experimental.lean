import Bakery.DMC3
import Bakery.command


import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub


universe u v



structure Conf where
  n : Nat
  m : Multiset Nat
instance : State Conf := ⟨⟩




namespace new

/--
`term` and `cond` are indices rather than fields so that they remain visible in
the type of a pattern.  In particular, when a pattern such as `p1` is used
against a ground term, Lean can unify the indexed term with that ground term
and infer the pattern's implicitly quantified variables.  Indexing `cond` also
lets dependent functions recover the symbolic constraint without storing or
proving it; if these were ordinary fields, the implicit variables would not
occur in the result type and could not be inferred this way.
-/
structure AtPatt {α : Type u} [State α] (term : α) (cond : Prop) where
--abbrev Patt {α : Type u} [State α] := List AtPatt


def p1 {n : Nat} {m : Multiset Nat} :
    AtPatt (α := Conf) ⟨n, m⟩ (n > 3) := ⟨⟩

/-- Both the ground term and its constraint are recovered from the indices. -/
def gMatch (ground : Conf) {cond : Prop}
    (_p : AtPatt ground cond) : Prop :=
  cond

example : gMatch ⟨4, ∅⟩ p1 := by
  simp [gMatch]

example : ¬gMatch ⟨3, ∅⟩ p1 := by
  simp [gMatch]

#check p1
#reduce p1
#reduce @p1
#reduce (fun (n : Nat) (m : Multiset Nat) ↦
  (⟨⟩ : AtPatt (α := Conf) ⟨n, m⟩ (n > 3)))


end new







namespace old1

-- atomic patterns
structure AtPatt (α : Type u) where
  {Vars : Type v}
  term : Vars → α
  cond : Vars → Prop
  --s {n : Nat} {m : Multiset Nat} : patt1 ⟨n, m⟩ (n > 3)

-- def patt1Anon : AtPatt Conf where
--   term := fun (x : Nat × Multiset Nat) =>
--     ⟨x.1, x.2⟩
--   cond := fun x =>
--     x.1 > 3

end old1

namespace old

abbrev Patt (α : Type u) [State α] := α → Prop → Prop
abbrev Rule (α : Type u) [State α] := α → α → Prop → Prop

inductive rule1 : Rule Conf where
  | mk {n : Nat} {m : Multiset Nat} : rule1 ⟨n, m⟩ ⟨n + 1, m⟩ (n < 5)

inductive patt1 : Patt Conf where
  | mk {n : Nat} {m : Multiset Nat} : patt1 ⟨n, m⟩ (n > 3)
#check @patt1.mk

inductive patt2 : Patt Conf where
  | mk {n : Nat} : patt2 ⟨n, ∅⟩ True

/-- Forward application of a rewriting rule to a constrained pattern.
    The result retains both the pattern constraint and the rule guard. -/
def applyRule {α : Type u} [State α]
    (rl : Rule α) (p : Patt α) : Patt α :=
  fun r h =>
    ∃ l pcond rcond,
      p l pcond ∧ rl l r rcond ∧ h = (pcond ∧ rcond)

example :
    applyRule rule1 patt1 ⟨5, ∅⟩ ((4 > 3) ∧ (4 < 5)) := by
  exact ⟨⟨4, ∅⟩, 4 > 3, 4 < 5, patt1.mk, rule1.mk, rfl⟩

#reduce applyRule rule1 patt1

instance {α : Type u} [State α] : Max (Patt α) where
  max p1 p2 := fun st cond => p1 st cond ∨ p2 st cond

#check (patt1 ⊔ patt2)

def Patt.Mem {α : Type u} [State α]
    (s : α) (p : Patt α) : Prop :=
  ∃ cond : Prop, p s cond ∧ cond

instance {α : Type u} [State α] :
    Membership α (Patt α) where
  mem p s := Patt.Mem s p

example : ⟨4, ∅⟩ ∈ patt1 := by
  refine ⟨_, patt1.mk, ?_⟩
  omega

example : ⟨4, ∅⟩ ∈ patt2 := by
  refine ⟨_, patt2.mk, ?_⟩
  trivial

example : ⟨4, ∅⟩ ∈ patt1 ⊔ patt2 := by
  refine ⟨_, Or.inl (patt1.mk), ?_⟩
  omega

example : patt1 ⊔ patt1 = patt1 := by
  funext st cond
  change (patt1 st cond ∨ patt1 st cond) = patt1 st cond
  apply propext
  simp

end old

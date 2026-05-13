import Mathlib.Logic.Relation

universe u

-- this is merely a marker class i.e. empty fields
class State (α : Type u) where

abbrev Pattern (α : Type u) [State α] := α → Prop

-- TODO: define ↑ from State to Pattern

-- (inductively defined) set of rules (i.e. Rewrite Theory)
abbrev Transition (α : Type u) [State α] := α → α → Prop

-- ⊔ for Transition for modular specification
def joinT {α : Type u} [State α] (t1 t2 : Transition α) : Transition α :=
  fun st st' => t1 st st' ∨ t2 st st'

-- notation t1 "⊔" t2 => joinT t1 t2 (fix this reserved notation)



-- Pattern → Pattern → Prop
abbrev PTransition (α : Type u) [State α] := (α → Prop) → (α → Prop) → Prop

-- (α → α → Prop) → ( (α → Prop) → (α → Prop) → Prop )
def stepUp {α : Type u} [State α] : Transition α → PTransition α :=
  fun t => fun p p' => ∀ st st', p st → t st st' → p' st'

--- System: State α with transition relation on α
class System (α : Type u) [State α] where
  step : α → α → Prop

-- structure Pattern (α : Type u) [State α] where
--   cond : α → Prop

-- def PStep (α : Type u) [State α] [System α] (p : Pattern α) (p' : Pattern α) : Prop :=
--   ∀ st st' : α, p.cond st → System.step st st' → p'.cond st'

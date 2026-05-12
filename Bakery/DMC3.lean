import Mathlib.Logic.Relation

universe u

-- this is merely a marker class i.e. empty fields
class State (α : Type u) where

--- System: State α with transition relation on α
class System (α : Type u) [State α] where
  step : α → α → Prop

structure Pattern (α : Type u) [State α] where
  cond : α → Prop

def PStep (α : Type u) [State α] [System α] (p : Pattern α) (p' : Pattern α) : Prop :=
  ∀ st st' : α, p.cond st → System.step st st' → p'.cond st'

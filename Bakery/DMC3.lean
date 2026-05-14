--import Mathlib.Logic.Relation
import Mathlib.Order.Lattice

universe u

-- this is merely a marker class i.e. empty fields
class State (α : Type u) where


/-
  **Pattern α** : α → Prop
-/

abbrev Pattern (α : Type u) [State α] := α → Prop

-- ⊔ for Patterns
def joinP {α : Type u} [State α] (p1 p2 : Pattern α) : Pattern α :=
  fun st => p1 st ∨ p2 st

instance {α : Type u} [State α] : Max (Pattern α) where
  max := joinP

-- define ↑ from State to Pattern
def stateUp {α : Type u} [State α] : α → Pattern α :=
  fun st => fun st' => st' = st

instance {α : Type u} [State α] : Coe α (Pattern α) where
  coe := stateUp


/-
  **Transition α** : α → α → Prop
-/
-- (inductively defined) set of rules (i.e. Rewrite Theory)
abbrev Transition (α : Type u) [State α] := α → α → Prop

-- ⊔ for Transitions
def joinT {α : Type u} [State α] (t1 t2 : Transition α) : Transition α :=
  fun st st' => t1 st st' ∨ t2 st st'

instance {α : Type u} [State α] : Max (Transition α) where
  max := joinT



/-
  **Transformer α** : Pattern α → Pattern α → Prop
  (Note) The term "transformer" may be misleading: it is a relation, not a function
-/
abbrev Transformer (α : Type u) [State α] := (α → Prop) → (α → Prop) → Prop

-- (α → α → Prop) → ( (α → Prop) → (α → Prop) → Prop )
def stepUp {α : Type u} [State α] : Transition α → Transformer α :=
  fun t => fun p p' => ∀ st st', p st → t st st' → p' st'

instance {α : Type u} [State α] : Coe (Transition α) (Transformer α) where
  coe := stepUp

-- ⊔ for Transformers
def joinPT {α : Type u} [State α] (t1 t2 : Transformer α) : Transformer α :=
  fun p p' => t1 p p' ∨ t2 p p'

instance {α : Type u} [State α] : Max (Transformer α) where
  max := joinPT

-- ⊓ for Transformers
def meetPT {α : Type u} [State α] (t1 t2 : Transformer α) : Transformer α :=
  fun p p' => t1 p p' ∧ t2 p p'

instance {α : Type u} [State α] : Min (Transformer α) where
  min := meetPT


/-
  System
-/
class System (α : Type u) [State α] where
  step : Transition α





/- Decomposition rule for transformers (bidirectional)
        p ⇒₁ p'     p ⇒₂ p'
      ======================= (TransComp)
          p (⇒₁ ⊔ ⇒₂) p'
-/
lemma TransComp {α : Type u} [State α] (t1 t2 : Transition α) (p p' : Pattern α) :
  (↑(t1 ⊔ t2) : Transformer α) p p' ↔ (↑t1 : Transformer α) p p' ∧ (↑t2 : Transformer α) p p' := by
  constructor
  -- If "joined" post-image of p is in p', then so are "individual" post-images
  · intro h
    exact ⟨fun st st' hp ht1 => h st st' hp (Or.inl ht1),
           fun st st' hp ht2 => h st st' hp (Or.inr ht2)⟩
  -- If "individual" post-images of p are in p', then so is the "joined" post-image
  · rintro ⟨h1, h2⟩ st st' hp (ht1 | ht2)
    · exact h1 st st' hp ht1
    · exact h2 st st' hp ht2

-- ↑(t1 ⊔ t2) = ↑t1 ⊓ ↑t2
-- To prove post-image safety w.r.t. a set of rules, we may decompose the proof into smaller pieces
lemma TransComp_eq {α : Type u} [State α] (t1 t2 : Transition α) :
  (↑(t1 ⊔ t2) : Transformer α) = (↑t1 : Transformer α) ⊓ (↑t2 : Transformer α) := by
  ext p p' -- using function extensionality axiom
  exact TransComp t1 t2 p p'

/- Decomposition rule for pre-conditions (bidirectional)
        p1 ⇒ p     p2 ⇒ p
      ====================== (PreComp)
          p1 ⊔ p2 ⇒ p
-/
lemma PreComp {α : Type u} [State α] (t : Transition α) (p p1 p2 : Pattern α) :
  (↑t : Transformer α) (p1 ⊔ p2) p ↔ (↑t : Transformer α) p1 p ∧ (↑t : Transformer α) p2 p := by
  constructor
  -- Forward (->): If it's safe from the union, it's safe from each individual part
  · intro h
    exact ⟨fun st st' hp1 ht => h st st' (Or.inl hp1) ht,
           fun st st' hp2 ht => h st st' (Or.inr hp2) ht⟩

  -- Backward (<-): If it's safe from both parts, it's safe from the union
  · rintro ⟨h1, h2⟩ st st' (hp1 | hp2) ht
    · exact h1 st st' hp1 ht
    · exact h2 st st' hp2 ht

/- Decomposition rule for post-conditions (unidirectional)
          p ⇒ p1
      ----------------- (PostComp)
        p ⇒ p1 ⊔ p2
-/
lemma PostComp {α : Type u} [State α] (t : Transition α) (p p1 p2 : Pattern α) :
  (↑t : Transformer α) p p1 ∨ (↑t : Transformer α) p p2 → (↑t : Transformer α) p (p1 ⊔ p2) := by
  -- Assume one of the transitions is strictly guaranteed
  rintro (h1 | h2) st st' hp ht
  -- Case 1: t guarantees p1
  · exact Or.inl (h1 st st' hp ht)
  -- Case 2: t guarantees p2
  · exact Or.inr (h2 st st' hp ht)

--import Mathlib.Logic.Relation
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

universe u

/-
  **α** = The type of States registered by user
  (merely a marker class i.e. empty fields)
-/
class State (α : Type u) where


/-
  **Pattern α** : α → Prop
-/

abbrev Pattern (α : Type u) [State α] := α → Prop

-- ⊥ for Patterns
instance {α : Type u} [State α] : Bot (Pattern α) where
  bot := fun _ => False

-- ⊔ for Patterns
instance {α : Type u} [State α] : Max (Pattern α) where
  max p1 p2 := fun st => p1 st ∨ p2 st

-- ↑ from State to Pattern
instance {α : Type u} [State α] : Coe α (Pattern α) where
  coe st := fun st' => st' = st

-- ≤ for Patterns
instance {α : Type u} [State α] : LE (Pattern α) where
  le p1 p2 := ∀ st, p1 st → p2 st

instance {α : Type u} [State α] : SemilatticeSup (Pattern α) where
  sup := max
  le := (· ≤ ·)

  le_refl := by
    intro p st hp
    exact hp
  le_trans := by
    intro p q r hpq hqr st hp
    exact hqr st (hpq st hp)
  le_antisymm := by
    intro p q hpq hqp
    funext st
    apply propext
    constructor
    · intro hp
      exact hpq st hp
    · intro hq
      exact hqp st hq
  le_sup_left := by
    intro p q st hp
    exact Or.inl hp
  le_sup_right := by
    intro p q st hq
    exact Or.inr hq
  sup_le := by
    intro p q r hpr hqr st hpq
    cases hpq with
    | inl hp => exact hpr st hp
    | inr hq => exact hqr st hq

instance {α : Type u} [State α] : OrderBot (Pattern α) where
  bot := ⊥
  bot_le := by
    intro pat st h_bot
    contradiction

/-
  **Transition α** : α → α → Prop
-/
abbrev Transition (α : Type u) [State α] := α → α → Prop

-- ⊔ for Transitions
instance {α : Type u} [State α] : Max (Transition α) where
  max t1 t2 := fun st st' => t1 st st' ∨ t2 st st'

-- ≤ for Transitions
instance {α : Type u} [State α] : LE (Transition α) where
  le t1 t2 := ∀ st st', t1 st st' → t2 st st'


/-
  **Transformer α** : Pattern α → Pattern α → Prop
  (Note) The term "transformer" may be misleading: it is a relation, not a function
  (Notation) p ⇒ p'
  (Definition) post(p) ⊆ p'
-/
abbrev Transformer (α : Type u) [State α] := (α → Prop) → (α → Prop) → Prop

-- ↑ from Transition α to Transformer α
instance {α : Type u} [State α] : Coe (Transition α) (Transformer α) where
  coe t := fun p p' => ∀ st st', p st → t st st' → p' st'

-- ⊔ for Transformers
instance {α : Type u} [State α] : Max (Transformer α) where
  max t1 t2 := fun p p' => t1 p p' ∨ t2 p p'

-- ⊓ for Transformers
instance {α : Type u} [State α] : Min (Transformer α) where
  min t1 t2 := fun p p' => t1 p p' ∧ t2 p p'


/-
  System
-/
class System (α : Type u) [State α] where
  step : Transition α





/- Decomposition rule for transformers (bidirectional)
        p ⇒₁ p'     p ⇒₂ p'
      ======================= (SComp)
          p (⇒₁ ⊔ ⇒₂) p'

  or equivalently: ↑(t1 ⊔ t2) = ↑t1 ⊓ ↑t2
-/
lemma SComp {α : Type u} [State α] (t1 t2 : Transition α) (p p' : Pattern α) :
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

lemma SComp' {α : Type u} [State α] (t1 t2 : Transition α) (p p' : Pattern α)
  (h_le : t1 ≤ t2) -- t1 is stricter than t2
  (h_safe : (↑t2 : Transformer α) p p') : -- t2 is safe
  (↑t1 : Transformer α) p p' := by
  intro st st' hp ht1
  exact h_safe st st' hp (h_le st st' ht1)

lemma SComp_eq {α : Type u} [State α] (t1 t2 : Transition α) :
  (↑(t1 ⊔ t2) : Transformer α) = (↑t1 : Transformer α) ⊓ (↑t2 : Transformer α) := by
  ext p p' -- using function extensionality axiom
  exact SComp t1 t2 p p'

/- Decomposition rule for LHS of Step (bidirectional)
        p1 ⇒ p     p2 ⇒ p
      ====================== (LComp)
          p1 ⊔ p2 ⇒ p
-/
lemma LComp {α : Type u} [State α] (t : Transition α) (p p1 p2 : Pattern α) :
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

/- Decomposition rule for RHS of Step (unidirectional)
          p ⇒ p1
      ----------------- (RComp)
        p ⇒ p1 ⊔ p2
-/
lemma RComp {α : Type u} [State α] (t : Transition α) (p p1 p2 : Pattern α) :
  (↑t : Transformer α) p p1 ∨ (↑t : Transformer α) p p2 → (↑t : Transformer α) p (p1 ⊔ p2) := by
  -- Assume one of the transitions is strictly guaranteed
  rintro (h1 | h2) st st' hp ht
  -- Case 1: t guarantees p1
  · exact Or.inl (h1 st st' hp ht)
  -- Case 2: t guarantees p2
  · exact Or.inr (h2 st st' hp ht)

/- Decomposition rule for RHS of Step (unidirectional)
        p ⇒ p'  p' ≤ p''
      -------------------- (RComp')
           p ⇒ p''
-/
lemma RComp' {α : Type u} [State α] (t : Transition α) (p p' p'' : Pattern α)
  (h_step : (↑t : Transformer α) p p')
  (h_le : p' ≤ p'') :
  (↑t : Transformer α) p p'' := by
  intro st st' hp ht
  exact h_le st' (h_step st st' hp ht)

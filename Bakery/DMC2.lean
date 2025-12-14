--- temporary file for refactoring DMC.lean
import Mathlib.Logic.Relation

universe u

--- System: Conf + step
class System (σ : Type u) where
  step : σ → σ → Prop

--- ISystem: System + init
class ISystem (σ : Type u) extends System σ where
  init : σ → Prop

abbrev steps {σ : Type u} [System σ] : σ → σ → Prop :=
  Relation.ReflTransGen (System.step (σ := σ))

infix:110 " ⇒ " => System.step
infix:110 " ⇒* " => steps

class IndInv (σ : Type u)
  (inv : σ → Prop)
  [S : ISystem σ] where
    base : ∀ cf : σ, S.init cf → inv cf
    ind : ∀ (cf cf' : σ), (inv cf ∧ (cf ⇒ cf')) → (inv cf')


--- Alternative definitions -- Bundled Approach (commented out) -/
-- structure System (σ : Type u) where
--   step : σ → σ → Prop

-- structure ISystem (σ : Type u) extends System σ where
--   init : σ → Prop

-- infix:110 " ⇒ " => System.step
-- Cons of bundled approach: need S as parameter to steps
-- def steps {σ} (S : System σ) : σ → σ → Prop := Relation.ReflTransGen S.step
-- infix:110 " ⇒* " => steps

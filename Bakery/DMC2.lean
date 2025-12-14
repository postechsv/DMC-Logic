--- temporary file for refactoring DMC.lean
import Mathlib.Logic.Relation

universe u

--- System: Conf + step
class System (σ : Type u) where
  step : σ → σ → Prop

--- ISystem: System + init
class ISystem (σ : Type u) [System σ] where
  init : σ → Prop

infix:110 " ⇒ " => System.step

/-- Reflexive-transitive closure of `⇒`. -/
abbrev steps {σ : Type u} [System σ] : σ → σ → Prop :=
  Relation.ReflTransGen (System.step (σ := σ))

infix:110 " ⇒* " => steps


-- class IndInv {σ : Type u} [System σ] (P : σ → Prop) : Prop where
--   base : ∀ {c : σ}, P c → P c
--   inv : ∀ {c c' : σ}, P c → (c ⇒ c') → P c'



-- Convenience lemmas you’ll use everywhere:

theorem steps_refl {σ} [System σ] (c : σ) : c ⇒* c :=
  Relation.ReflTransGen.refl

theorem steps_single {σ} [System σ] {c c' : σ} (h : c ⇒ c') : c ⇒* c' :=
  Relation.ReflTransGen.single h

theorem steps_trans {σ} [System σ] {a b c : σ} :
    a ⇒* b → b ⇒* c → a ⇒* c :=
  Relation.ReflTransGen.trans

---end System

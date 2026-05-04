import Mathlib.Logic.Relation

--- TODO: this could be abstracted as a typeclass to be instantiated by
--- standard "computational" model of CCSA (a la Bana & Comon)
--- where world  =  non-negligible set of random tapes
---   and w R v <=> w superset of v
structure KripkeFrame where
  World : Type
  R : World → World → Prop
  refl : Reflexive R
  trans : Transitive R

def MProp (K : KripkeFrame) := K.World → Prop

def box {K : KripkeFrame} (P : MProp K) : MProp K :=
  fun w => ∀ v, K.R w v → P v

def diamond {K : KripkeFrame} (P : MProp K) : MProp K :=
  fun w => ∃ v, K.R w v ∧ P v

notation:max "□" P:max => box P
notation:max "⋄" P:max => diamond P

-- M, S ⊨ ϕ ∧ ψ  iff  M, S ⊨ ϕ  and  M, S ⊨ ψ
def mand {K : KripkeFrame} (ϕ ψ : MProp K) : MProp K :=
  fun w => ϕ w ∧ ψ w

-- M, S ⊨ ϕ ∨ ψ  iff  M, S ⊨ ϕ  or  M, S ⊨ ψ
def mor {K : KripkeFrame} (ϕ ψ : MProp K) : MProp K :=
  fun w => ϕ w ∨ ψ w

-- M, S ⊨ ¬ϕ  iff  M, S ⊭ ϕ
def mnot {K : KripkeFrame} (ϕ : MProp K) : MProp K :=
  fun w => ¬(ϕ w)

-- M, S ⊨ ∀x.ϕ  iff  for all a ∈ D, M, S, ν[x ↦ a] ⊨ ϕ
def mforall {K : KripkeFrame} {D : Type} (ϕ : D → MProp K) : MProp K :=
  fun w => ∀ (a : D), ϕ a w

-- M, S ⊨ ∃x.ϕ  iff  there exists a ∈ D such that M, S, ν[x ↦ a] ⊨ ϕ
def mexists {K : KripkeFrame} {D : Type} (ϕ : D → MProp K) : MProp K :=
  fun w => ∃ (a : D), ϕ a w

def mimpl {K : KripkeFrame} (ϕ ψ : MProp K) : MProp K :=
  fun w => ϕ w → ψ w

infix:35 " ⋏ " => mand
infix:30 " ⋎ " => mor
prefix:max "∼" => mnot
infixr:70 " ⊃ " => mimpl


-- K (Distribution)
lemma axiom_K {F : KripkeFrame} (P Q : MProp F) (w : F.World) :
  (□(P ⊃ Q)) w → ((□ P) ⊃ (□ Q)) w := by
  intro hBoxPQ hBoxP v hwv
  exact (hBoxPQ v hwv) (hBoxP v hwv)

--- T (Truth/Reflexivity)
lemma axiom_T {K : KripkeFrame} (P : MProp K) (w : K.World) : (□ P) w → P w := by
  intro hBox
  exact hBox w (K.refl w)

-- 4 (Transitivity)
lemma axiom_4 {F : KripkeFrame} (P : MProp F) (w : F.World) :
  (□ P) w → (□□ P) w := by
  intro hBox v hwv u hvu
  have hwu : F.R w u := F.trans hwv hvu
  exact hBox u hwu



lemma necessitation {F : KripkeFrame} (P : MProp F) :
  (∀ w, P w) → (∀ w, (□ P) w) := by
  intro hValid w v _
  -- Since P is true in EVERY world (`hValid`), it is trivially true in `v`.
  -- We don't even need to look at the accessibility relation!
  exact hValid v

import Mathlib.Logic.Relation

--- TODO: this could be abstracted as a typeclass to be instantiated by
--- standard "computational" model of CCSA (a la Bana & Comon)
--- where world  =  non-negligible set of random tapes
---   and w R v <=> w superset of v
--- TODO: should be called RootedKripkeFrame
structure KripkeFrame where
  World : Type
  R : World → World → Prop
  refl : Reflexive R
  trans : Transitive R
  root : World
  min : ∀ w, R root w

def MProp (K : KripkeFrame) := K.World → Prop

def box {K : KripkeFrame} (P : MProp K) : MProp K :=
  fun w => ∀ v, K.R w v → P v

def diamond {K : KripkeFrame} (P : MProp K) : MProp K :=
  fun w => ∃ v, K.R w v ∧ P v

notation:max "□" P:max => box P
notation:max "⋄" P:max => diamond P

-- Modal True: A function that returns standard True in every world
def mtrue {K : KripkeFrame} : MProp K :=
  fun _ => True

-- Modal False: A function that returns standard False in every world
def mfalse {K : KripkeFrame} : MProp K :=
  fun _ => False

-- Standard notation for Top (True) and Bottom (False)
-- notation " ⊤ " => mtrue
-- notation " ⊥ " => mfalse

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

-- Modal Implication
def mimp {K : KripkeFrame} (p q : MProp K) : MProp K :=
  fun w => p w → q w

-- Modal Biconditional (Iff)
def miff {K : KripkeFrame} (p q : MProp K) : MProp K :=
  fun w => p w ↔ q w

infixr:35 " ⋏ " => mand
infixr:30 " ⋎ " => mor
prefix:max "∼" => mnot
infixr:70 " ⊃ " => mimpl
notation:20 w " ⊨ₛ₄ " p => p w
notation:50 p " ⤇ " q => mimp p q
notation:50 p " ⇔ " q => miff p q


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


--- w r w' ∧ w ⊨ₛ₄ □⋄p → w ⊨ₛ₄ □⋄p
lemma persist_ow {K : KripkeFrame} {P : K.World → Prop} {w w' : K.World}
    (h_R : K.R w w') (h_boxdia : □⋄P w) : □⋄P w' := by
  intro v h_w'_v
  have h_w_v : K.R w v := K.trans h_R h_w'_v
  exact h_boxdia v h_w_v

lemma box_imp_box_dia {K : KripkeFrame} {P : K.World → Prop} {w : K.World}
    (h_box : □ P w) : □⋄ P w := by
  intro w' h_w_w'
  use w'
  constructor
  · exact K.refl w'
  · exact h_box w' h_w_w'

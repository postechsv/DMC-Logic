import Mathlib.Logic.Relation

class IndInv (Conf : Type) (inv : Conf → Prop)
  (init : Conf → Prop) (step : Conf → Conf → Prop) where
    base : ∀ cf : Conf, init cf → inv cf
    ind : ∀ (cf cf' : Conf), (inv cf ∧ (step cf cf')) → (inv cf')

variable {Conf : Type}
variable {inv init : Conf → Prop}
variable {step : Conf → Conf → Prop}

theorem invariant
    [hInv : IndInv Conf inv init step]
    {cf cf' : Conf}
    (h0 : init cf)
    (hrt : Relation.ReflTransGen step cf cf') :
    inv cf' := by
  induction hrt with
  | refl =>
      -- this case is cf' = cf
      -- so we just use base
      have : inv cf := hInv.base cf h0
      -- x is definitionaly cf, so:
      simpa using this
  | tail hxy hyz ih =>
      -- hxy : ReflTransGen step cf ?y
      -- hyz : step ?y ?z
      -- ih  : pred ?y
      have hpair : inv _ ∧ step _ _ := ⟨ih, hyz⟩
      exact hInv.ind _ _ hpair

-- --- Conjunction of invariants is an invariant
-- instance IndInvConj
--     (pred₁ pred₂ init step)
--     [h1 : IndInv pred₁ init step]
--     [h2 : IndInv pred₂ init step] :
--     IndInv (fun cf => pred₁ cf ∧ pred₂ cf) init step where
--   base cf h0 :=
--     ⟨h1.base cf h0, h2.base cf h0⟩
--   ind cf cf' h := by
--     rcases h with ⟨⟨hp1, hp2⟩, hstep⟩
--     exact ⟨h1.ind cf cf' ⟨hp1, hstep⟩, h2.ind cf cf' ⟨hp2, hstep⟩⟩

--- “Safety” meta-theorem: no bad state is reachable
def Safe (init : Conf → Prop) (step : Conf → Conf → Prop) (Bad : Conf → Prop) : Prop :=
  ∀ cf cf', init cf → Relation.ReflTransGen step cf cf' → ¬ Bad cf'

theorem IndInv.safe
    {inv init safe_pred : Conf → Prop} {step : Conf → Conf → Prop}
    [IndInv Conf inv init step]
    (invSafe : ∀ cf, inv cf → safe_pred cf) :
    ∀ cf cf', init cf → Relation.ReflTransGen step cf cf' → safe_pred cf' := by
  intro cf cf' h0 hreach
  -- from inductive invariant:
  have hp : inv cf' :=
    invariant (inv:=inv) (init:=init) (step:=step) h0 hreach
  exact invSafe cf' hp


theorem IndInv.safe1
    {inv init : Conf → Prop} {step : Conf → Conf → Prop}
    [IndInv Conf inv init step]
    (Bad : Conf → Prop)
    (hExclude : ∀ cf, inv cf → ¬ Bad cf) :
    Safe init step Bad := by
  intro cf cf' h0 hreach
  -- from inductive invariant:
  have hp : inv cf' :=
    invariant (inv:=inv) (init:=init) (step:=step) h0 hreach
  exact hExclude cf' hp


-- --- Restricting the initial set
-- theorem IndInv.restrict_init
--     {pred init init' : Conf → Prop} {step : Conf → Conf → Prop}
--     [hInv : IndInv pred init step]
--     (hSub : ∀ cf, init' cf → init cf) :
--     IndInv pred init' step where
--   base cf h0 :=
--     hInv.base cf (hSub cf h0)
--   ind cf cf' h :=
--     hInv.ind cf cf' h

-- --- Invariants for an equivalent step relation
-- theorem IndInv.congr_step
--     {pred init : Conf → Prop}
--     {step₁ step₂ : Conf → Conf → Prop}
--     (hEq : ∀ cf cf', step₁ cf cf' ↔ step₂ cf cf')
--     [hInv : IndInv pred init step₁] :
--     IndInv pred init step₂ where
--   base cf h0 := hInv.base cf h0
--   ind cf cf' h := by
--     -- h : pred cf ∧ step₂ cf cf'
--     have h' : pred cf ∧ step₁ cf cf' :=
--       ⟨h.1, (hEq cf cf').mpr h.2⟩
--     -- reuse old instance
--     exact hInv.ind cf cf' h'

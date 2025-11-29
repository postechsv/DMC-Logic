import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Logic.Relation

inductive Mode where
  | idle
  | wait : Nat → Mode
  | crit : Nat → Mode


inductive Proc where
  | proc : Mode → Proc


notation "$[" m "]" => Proc.proc m

abbrev ProcSet := Multiset Proc

structure Conf where
  t : Nat
  s : Nat
  c : ProcSet

open Mode Proc Nat
open scoped Multiset

inductive Step : Conf → Conf → Prop where
  | wake : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n,      s := m, c := {$[idle]}   + ps}
           {t := succ n, s := m, c := {$[wait n]} + ps}
  | crit : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n, s := m, c := {$[wait m]} + ps}
           {t := n, s := m, c := {$[crit m]} + ps}
  | exit : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n, s := m,      c := {$[crit m]} + ps}
           {t := n, s := succ m, c := {$[idle]} + ps}

infix:110 " ⇒ " => Step
infix:110 " ⇒* " => Relation.ReflTransGen Step

#check Step
#check ({$[idle]} : ProcSet)
#check {$[idle]} + {$[idle]}

def init1 : Conf :=
  {t := 0, s := 0, c := {$[idle]}}

def init2 : Conf :=
  {t := 0, s := 0, c := {$[idle], $[idle]}}


variable (n m k : Nat)
variable (ps : ProcSet)
variable (cf : Conf)


example : init1 ⇒* init1 := by
  apply Relation.ReflTransGen.refl


example : init1 ⇒* {t := 1, s := 0, c := {$[wait 0]}} := by
  apply Relation.ReflTransGen.single
  · apply Step.wake 0 0 0


example : init1 ⇒* {t := 1, s := 0, c := {$[crit 0]}} := by
  apply Relation.ReflTransGen.trans
  · apply Relation.ReflTransGen.single
    apply Step.wake 0 0 0
  · apply Relation.ReflTransGen.single
    apply Step.crit


example : init2 ⇒* {t := 2, s := 0, c := {$[wait 1], $[wait 0]}} := by
  apply Relation.ReflTransGen.trans
  · apply Relation.ReflTransGen.single
    apply Step.wake 0 0 {$[idle]}
  · apply Relation.ReflTransGen.single
    rw [Multiset.add_comm]
    apply Step.wake

--- all proces are idle
def is (ps : ProcSet) :=
  ∀m ∈ ps, m = $[idle]

--- all procs are either idle or waiting
def ws (ps : ProcSet) :=
  ∀m ∈ ps, (m = $[idle] ∨ ∃ n, m = $[wait n])

def Proc.ticket? : Proc → Option Nat
  | $[wait n] => some n
  | $[crit n] => some n
  | $[idle]   => none

--- return the set of all ticket numbers in a procset
def tickets (ps : ProcSet) : Multiset Nat := ps.filterMap Proc.ticket?

#eval tickets {$[idle], $[wait 3], $[crit 5], $[wait 3]} = {3, 5, 3}

example : ¬(is ($[wait m] ::ₘ ps)) := by
  unfold is
  simp


---------------------
--- Useful Lemmas ---
---------------------

lemma tickets_up :
  ∀ (p: Proc) (ps: ProcSet) (k: Nat),
    k ∈ tickets ps →
    k ∈ tickets (p ::ₘ ps) := by
  intro p ps k hk
  simp [tickets] at *; right; apply hk


lemma tickets_down :
  ∀ (p: Proc) (ps: ProcSet) (k: Nat),
    k ∈ tickets (p ::ₘ ps) →
    (p.ticket? = some k ∨ k ∈ tickets ps) := by
  intro p ps k hk
  simp [tickets] at hk
  rcases hk with hk1 | hk2
  · exact Or.inl hk1
  · right; simpa [tickets]


lemma nodup_up {p : Proc} {ps : ProcSet} (k : Nat) :
  (p.ticket? = some k) →
    (k ∉ tickets ps) →
    (tickets ps).Nodup →
    (tickets (p ::ₘ ps)).Nodup := by
  intro h1 h2 h3
  have hpair : k ∉ tickets ps ∧ (tickets ps).Nodup := ⟨h2, h3⟩
  simpa [tickets, h1, Multiset.nodup_cons] using hpair


lemma nodup_down :
  ∀ (p : Proc) (ps : ProcSet), (tickets (p ::ₘ ps)).Nodup →
      (tickets ps).Nodup := by
  intro p ps h
  apply Multiset.nodup_of_le _ h
  simp [tickets]
  cases htp : ticket? p with
  | none => simp [htp]
  | some k => simp [htp]; exact Multiset.le_cons_self _ _


lemma freshness :
  ∀ (p : Proc) (ps : ProcSet) (n: Nat), (tickets (p ::ₘ ps)).Nodup →
    (p = $[wait n] ∨ p = $[crit n]) → n ∉ tickets ps := by
  intro p ps n h1 h2 h3
  have hp_ticket : ticket? p = some n := by
    cases h2 with
    | inl hw => simp [hw, ticket?]
    | inr hc => simp [hc, ticket?]
  have hnodup : (n ::ₘ tickets ps).Nodup := by
    simpa [tickets, hp_ticket] using h1
  have hn_not : n ∉ tickets ps :=
    (Multiset.nodup_cons.1 hnodup).1
  exact hn_not h3

lemma no_nat_between (m k : ℕ) (h : m < k ∧ k < m + 1) : False := by
  have hmk : m < k := h.1
  have hkm1 : k < m + 1 := h.2
  -- rewrite m + 1 as succ
  have hkm_succ : k < m.succ := by
    simpa [Nat.succ_eq_add_one] using hkm1
  -- from k < m.succ we get k ≤ m
  have hkm_le : k ≤ m := (Nat.lt_succ_iff.mp hkm_succ)
  -- chain m < k ≤ m to get m < m
  have hmm : m < m := lt_of_lt_of_le hmk hkm_le
  exact lt_irrefl _ hmm



lemma is_of_no_tickets
  (ps : ProcSet)
  (hk_false : ∀ k ∈ tickets ps, False) :
  is ps := by
  intro m hm
  -- m : Proc
  -- split on Proc first
  cases m with
  | proc mode =>
      -- now mode : Mode
      cases mode with
      | idle => rfl
      | wait n => sorry
      | crit n => sorry
          -- m = $[Mode.crit n]
          -- have : n ∈ tickets ps := by
          --   classical
          --   dsimp [tickets]
          --   apply (Multiset.mem_filterMap.2 ?_)
          --   refine ⟨$[Mode.crit n], hm, ?_⟩
          --   simp [Proc.ticket?]     -- ticket? $[crit n] = some n
          -- exact (hk_false n this).elim


lemma is_cons_idle_of_no_tickets
  (ps : ProcSet)
  (hk_false : ∀ k ∈ tickets ps, False) :
  is ($[idle] ::ₘ ps) := by
  have his : is ps := is_of_no_tickets ps hk_false
  intro m hm
  have hcases : m = $[idle] ∨ m ∈ ps := by
    simpa [Multiset.mem_cons] using hm
  cases hcases with
  | inl h => simp [h]
  | inr hmps => exact his m hmps


----------------------------
--- Inductive Invariants ---
----------------------------

def init_pred (cf : Conf) : Prop :=
  cf.t = cf.s ∧ is cf.c

#check init_pred

def wait_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧ ws cf.c ∧ (∀ k ∈ tickets cf.c, k ≥ cf.s ∧ k < cf.t) ∧ ((tickets cf.c).Nodup)


def crit_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧
  ∃ ps : ProcSet,
    cf.c = {$[crit cf.s]} + ps ∧
    ws ps ∧
    (∀ k ∈ tickets ps, k > cf.s ∧ k < cf.t) ∧
    ((tickets ps).Nodup)


lemma init_wait {cf cf' : Conf} :
    (init_pred cf ∧ (cf ⇒ cf')) →
    wait_pred cf' := by
  simp [init_pred, wait_pred, is, ws]
  intro hts his hstep
  cases hstep with
  | crit n m ps => simp at *
  | exit n m ps => simp at *
  | wake n m ps =>
      simp at *
      simp [hts]
      constructor
      · intro ha hha
        apply his at hha
        exact Or.inl hha
      · constructor
        · intro k hk
          simp [tickets, ticket?] at hk
          rcases hk with hA | hB
          · simp [hA]
          · rcases hB with ⟨a, ⟨ha, ha'⟩⟩
            apply his at ha
            simp [ha] at ha'
        · have hps: tickets ps = Multiset.zero := by
            induction ps using Multiset.induction_on with
            | empty => simp [tickets]; rfl
            | @cons p ps ih =>
                simp at his
                have h1 := his.1
                have h2 := ih his.2
                simp [h1, ←h2, tickets, ticket?]
          apply nodup_up m
          · simp [ticket?]
          · simp [hps]; intro hm; rcases hm
          · simp [hps]; apply Multiset.nodup_zero

lemma wait_waitOrCrit {cf cf' : Conf} :
    (wait_pred cf ∧ (cf ⇒ cf')) →
    (wait_pred cf' ∨ crit_pred cf') := by
  intro ⟨⟨hts,hws,⟨hrange, hnodup⟩⟩, hstep⟩
  cases hstep with
  | crit n m ps =>
    simp at * ; right ; simp [crit_pred]
    constructor
    · apply hts
    constructor
    · simp [ws] at * ; exact hws
    · simp [ws] at *
      constructor
      · intro k hk
        have h : m ∉ tickets ps
          := (freshness $[wait m] ps m hnodup (Or.inl rfl))
        have h' : k ∈ tickets ($[wait m] ::ₘ ps)
          := (tickets_up $[wait m] ps k hk)
        apply hrange at h'
        have hm : m ≠ k := by
          intro hmkeq; apply h; simpa [hmkeq]
        exact ⟨lt_of_le_of_ne h'.1 hm, h'.right⟩
      · exact (nodup_down $[wait m] ps hnodup)
  | exit n m ps => simp [ws] at *
  | wake n m ps =>
    simp [wait_pred] at *; left
    constructor
    · exact (lt_trans hts (Nat.lt_succ_self n))
    constructor
    · simp [ws] at *; apply hws
    constructor
    · intro k hk
      have hk' := hrange k
      apply tickets_down at hk
      rcases hk with hkA | hkB
      · simp [ticket?] at hkA
        constructor
        · rw [←hkA]; apply le_of_lt hts
        · rw [hkA]; apply lt_succ_self k
      · apply (tickets_up $[idle] ps) at hkB
        apply hk' at hkB
        exact ⟨hkB.1, lt_trans hkB.2 (Nat.lt_succ_self n)⟩
    · apply nodup_up
      · simp [ticket?]; rfl
      · intro hn
        apply tickets_up $[idle] ps at hn
        apply hrange at hn
        exact lt_irrefl n hn.2
      · exact nodup_down $[idle] ps hnodup

lemma crit_initOrWaitOrCrit {cf cf' : Conf} :
    (crit_pred cf ∧ (cf ⇒ cf')) →
    (init_pred cf' ∨ wait_pred cf' ∨ crit_pred cf') := by
  intro ⟨⟨hts,ps',h1,hws,hk,hnodup⟩,hstep⟩
  cases hstep with
  | crit n m ps =>
      simp at *
      have hw_in_left : $[wait m] ∈ ($[wait m] ::ₘ ps : ProcSet) := by
        simp
      have hw_in_right : $[wait m] ∈ ($[crit m] ::ₘ ps' : ProcSet) := by
        simpa [h1] using hw_in_left
      have hps' : $[wait m] ∈ ps' := by
        rcases Multiset.mem_cons.mp hw_in_right with h_eq | h_mem
        · cases h_eq
        · exact h_mem
      have hm : m ∈ tickets ps' := by
        simp [tickets]
        exists $[wait m]
      apply hk at hm; simp at hm
  | exit n m ps =>
      simp at *
      · by_cases hmn : m + 1 = n
        · left; simp [←hmn, init_pred] at *
          have hk_false : ∀ k ∈ tickets ps', False := by
            intro k hk'
            exact no_nat_between m k (hk k hk')
          rw [←h1] at hk_false
          have : is ($[idle] ::ₘ ps) :=
            is_cons_idle_of_no_tickets ps hk_false
          apply this
        · right; left; simp [wait_pred]
          constructor
          · have hlt : m + 1 < n := by
              have hle : m + 1 ≤ n := by
                simpa [Nat.succ_eq_add_one] using Nat.succ_le_of_lt hts
              exact lt_of_le_of_ne hle hmn
            exact hlt
          constructor
          · simp [ws] at *; simpa [hws, h1]
          constructor
          · intro k hk'
            apply tickets_down $[idle] ps at hk'
            rcases hk' with hk'A | hk'B
            · simp [ticket?] at hk'A
            · rw [h1] at hk'B
              apply hk at hk'B
              exact ⟨by
                have := Nat.succ_le_of_lt hk'B.1
                simpa [Nat.succ_eq_add_one] using this,
              hk'B.2⟩
          · rw [←h1] at hnodup
            simpa [tickets, Proc.ticket?] using hnodup
  | wake n m ps =>
      simp at *; right; right
      simp [crit_pred]
      constructor
      · exact (lt_trans hts (Nat.lt_succ_self n))
      · have hps'' : ∃ps'' : ProcSet, ps = $[crit m] ::ₘ ps'' := by
          have hcrit_R : $[Mode.crit m] ∈ ($[Mode.crit m] ::ₘ ps') := by
            simp
          have hcrit_L : $[Mode.crit m] ∈ ($[Mode.idle] ::ₘ ps) := by
            simpa [h1] using hcrit_R
          have hcrit_cases : $[Mode.crit m] = $[Mode.idle] ∨ $[Mode.crit m] ∈ ps :=
            (Multiset.mem_cons).1 hcrit_L
          have hcrit_ps : $[Mode.crit m] ∈ ps := by
            cases hcrit_cases with
            | inl h => cases h
            | inr h => exact h
          obtain ⟨ps'', hps''⟩ := Multiset.exists_cons_of_mem hcrit_ps
          exact ⟨ps'', hps''⟩
        rcases hps'' with ⟨ps'',hps''1⟩
        have hps''2 : ps' = $[idle] ::ₘ ps'' := by
          have h1' :
            $[idle] ::ₘ $[crit m] ::ₘ ps'' = $[crit m] ::ₘ ps' := by
            simpa [hps''1] using h1
          have h1'' :
            $[crit m] ::ₘ $[idle] ::ₘ ps'' = $[crit m] ::ₘ ps' := by
            simpa [Multiset.cons_swap] using h1'
          have hps' : $[idle] ::ₘ ps'' = ps' := by
            simpa [Multiset.cons_eq_cons] using h1''
          simp [hps']
        exists $[wait n] ::ₘ ps''
        constructor
        · simp [hps''1]
          exact Multiset.cons_swap _ _ _
        constructor
        · simp [ws]
          simpa [ws, hps''2] using hws
        constructor
        · intro k hk'
          rw [hps''2] at hk
          simp [tickets] at hk'
          rcases hk' with hk'A | hk'B
          · simp [ticket?] at hk'A -- n = k
            rw [←hk'A]; simpa
          · simp [tickets] at hk
            have hk := hk k
            have hk := hk (Or.inr hk'B)
            exact ⟨hk.1, lt_trans hk.2 (Nat.lt_succ_self _)⟩
        · apply nodup_up
          · simp [ticket?]; rfl
          · intro hn
            have hn' : n ∈ tickets ps' := by
              -- rewrite ps' and simplify tickets on cons idle
              simpa [tickets, hps''2, Proc.ticket?] using hn

            -- now apply hk at k = n
            have hbounds : m < n ∧ n < n := hk n hn'
            have hlt : n < n := hbounds.2
            exact lt_irrefl _ hlt
          · rw [hps''2] at hnodup
            simpa [tickets, Proc.ticket?] using hnodup



def inv_pred (cf : Conf) : Prop :=
  init_pred cf ∨ wait_pred cf ∨ crit_pred cf

lemma inv_ind {cf cf' : Conf} :
    (inv_pred cf ∧ (cf ⇒ cf')) →
    (inv_pred cf') := by sorry

def mutex_pred (cf : Conf) : Prop := sorry

lemma inv_mutex : ∀ (cf : Conf), inv_pred cf → mutex_pred cf := sorry

theorem bakery_mutex {cf cf' : Conf} :
    (init_pred cf ∧ (cf ⇒* cf')) →
    (mutex_pred cf') := by sorry




-----------------------
--- Meta Properties ---
-----------------------


class IndInv (pred : Conf → Prop) (init : Conf → Prop) (step : Conf → Conf → Prop) where
    base : ∀ cf : Conf, init cf → pred cf
    ind : ∀ (cf cf' : Conf), (pred cf ∧ (step cf cf')) → (pred cf')

variable {pred init : Conf → Prop}
variable {step : Conf → Conf → Prop}

theorem invariant
    [hInv : IndInv pred init step]
    {cf cf' : Conf}
    (h0 : init cf)
    (hrt : Relation.ReflTransGen step cf cf') :
    pred cf' := by
  induction hrt with
  | refl =>
      -- this case is cf' = cf
      -- so we just use base
      have : pred cf := hInv.base cf h0
      -- x is definitionaly cf, so:
      simpa using this
  | tail hxy hyz ih =>
      -- hxy : ReflTransGen step cf ?y
      -- hyz : step ?y ?z
      -- ih  : pred ?y
      have hpair : pred _ ∧ step _ _ := ⟨ih, hyz⟩
      exact hInv.ind _ _ hpair

--- Conjunction of invariants is an invariant
instance IndInvConj
    (pred₁ pred₂ init step)
    [h1 : IndInv pred₁ init step]
    [h2 : IndInv pred₂ init step] :
    IndInv (fun cf => pred₁ cf ∧ pred₂ cf) init step where
  base cf h0 :=
    ⟨h1.base cf h0, h2.base cf h0⟩
  ind cf cf' h := by
    rcases h with ⟨⟨hp1, hp2⟩, hstep⟩
    exact ⟨h1.ind cf cf' ⟨hp1, hstep⟩, h2.ind cf cf' ⟨hp2, hstep⟩⟩

--- “Safety” meta-theorem: no bad state is reachable
def Safe (init : Conf → Prop) (step : Conf → Conf → Prop) (Bad : Conf → Prop) : Prop :=
  ∀ cf cf', init cf → Relation.ReflTransGen step cf cf' → ¬ Bad cf'

theorem IndInv.safe
    {pred init : Conf → Prop} {step : Conf → Conf → Prop}
    [IndInv pred init step]
    (Bad : Conf → Prop)
    (hExclude : ∀ cf, pred cf → ¬ Bad cf) :
    Safe init step Bad := by
  intro cf cf' h0 hreach
  -- from inductive invariant:
  have hp : pred cf' :=
    invariant (pred:=pred) (init:=init) (step:=step) h0 hreach
  exact hExclude cf' hp


--- Restricting the initial set
theorem IndInv.restrict_init
    {pred init init' : Conf → Prop} {step : Conf → Conf → Prop}
    [hInv : IndInv pred init step]
    (hSub : ∀ cf, init' cf → init cf) :
    IndInv pred init' step where
  base cf h0 :=
    hInv.base cf (hSub cf h0)
  ind cf cf' h :=
    hInv.ind cf cf' h

--- Invariants for an equivalent step relation
theorem IndInv.congr_step
    {pred init : Conf → Prop}
    {step₁ step₂ : Conf → Conf → Prop}
    (hEq : ∀ cf cf', step₁ cf cf' ↔ step₂ cf cf')
    [hInv : IndInv pred init step₁] :
    IndInv pred init step₂ where
  base cf h0 := hInv.base cf h0
  ind cf cf' h := by
    -- h : pred cf ∧ step₂ cf cf'
    have h' : pred cf ∧ step₁ cf cf' :=
      ⟨h.1, (hEq cf cf').mpr h.2⟩
    -- reuse old instance
    exact hInv.ind cf cf' h'

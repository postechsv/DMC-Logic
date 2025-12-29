# Tutorial

## representing rewrite theries in Lean
The rewrite rules for bakery algorithm can be encoded as 
the following inductive type `Step` in Lean.
```
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
```

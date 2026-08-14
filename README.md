# PosCheck
## Pattern-Oriented Symbolic Model Checker
- Inspired by DM-Check tool
- conPanna (Constrained Pattern Narrowing)

## Examples
Milestone examples
- bakery.lean (depends on Bakery/DMC.lean)
- nsl-computational.lean (depends on Bakery/S4.lean)

Working examples
- qlock-compositional (depends on Bakery/DMC3.lean)
  - RComp, LComp, SComp
  - c.f., mono-vs-modu.lean (modular specification demo)

- unification (depends on Bakery/DMC3.lean)
  - certifying unifier completeness given by Maude

- ClientServer (depends on Bakery/DMC3.lean)
  - compositional verification (PComp)

- pretheorem
  - patterns & rules as lambda closures
  - pretheorems for dynamic generation of proof obligations by getMGUs tactic
import Lib.Ulm.Theorem

/-!
# Axiom gate for Ulm's theorem

A `sorry`-free source tree is not the same claim as a `sorry`-free proof: a hole
anywhere in the transitive proof term shows up as `sorryAx` in the kernel's axiom
list, whatever the source text says, and Lean's editor checkmarks do **not** catch
a `sorry` in a dependency. Grepping cannot see it either.

`#guard_msgs` compares the printed axiom list against the expected one, so if a
hole, a new axiom, or a dependency on unfinished work ever enters the proof of
`ulm_theorem` or either of its directions, **this file fails to compile**.

The expected list is Lean's three standard axioms. `sorryAx` must never appear.
-/

/-- info: 'ulm_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ulm_theorem

/-- info: 'ulm_invariants_of_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ulm_invariants_of_iso

/-- info: 'iso_of_ulm_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iso_of_ulm_invariants

import Lib.Ulm.Classification
import Lib.Ulm.Invariance

/-!
# Ulm's theorem

Public entry point for the Ulm-theorem track of the project.
-/

open Cardinal Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

/-- The canonical model: given a function `f : Ordinal → ℕ` of finite Ulm
invariants in the countable case, construct a reduced p-group realizing them. -/
axiom canonicalModel (f : Ordinal → ℕ) : Type u

/-- Ulm's theorem: two countable reduced abelian p-groups are isomorphic iff
their Ulm invariants agree. -/
theorem ulm_theorem {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H) :
    Nonempty (G ≃+ H) ↔
    ∀ α : Ordinal, ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  constructor
  · rintro ⟨φ⟩ α
    exact ulmInvariant_iso_invariant (p := p) φ α
  · intro h
    exact iso_of_ulmInvariant_eq (p := p) hGred hHred h

import Lib.Ulm.Classification
import Lib.Ulm.Invariance

/-!
# Ulm's theorem

Public entry point for the Ulm-theorem track of the project.
-/

open Cardinal Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

/-- Legacy placeholder for a realization theorem from a classical Ulm-invariant profile.
This is not used by the current Ulm-theorem proof path. -/
axiom canonicalModel (f : Ordinal → Cardinal) : Type u

/-- Public easy direction of Ulm's theorem: an isomorphism preserves all classical Ulm invariants. -/
theorem ulm_invariants_of_iso {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (hiso : Nonempty (G ≃+ H)) :
    ∀ α : Ordinal, ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  rcases hiso with ⟨φ⟩
  intro α
  exact ulmInvariant_iso_invariant (p := p) φ α

/-- Public hard direction of Ulm's theorem: equal classical Ulm invariants imply isomorphism
for countable reduced abelian `p`-groups. -/
theorem iso_of_ulm_invariants {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal, ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) := by
  exact iso_of_ulmInvariant_eq (p := p) hGred hHred hinv

/-- Named forward direction for running the proof in two separate parts. -/
theorem ulm_theorem_forward {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (hiso : Nonempty (G ≃+ H)) :
    ∀ α : Ordinal, ulmInvariant p α (G := G) = ulmInvariant p α (G := H) :=
  ulm_invariants_of_iso (p := p) hiso

/-- Named backward direction for running the proof in two separate parts. -/
theorem ulm_theorem_backward {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal, ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) :=
  iso_of_ulm_invariants (p := p) hGred hHred hinv

/-- Ulm's theorem: two countable reduced abelian p-groups are isomorphic iff
their classical Ulm invariants agree. -/
theorem ulm_theorem {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H) :
    Nonempty (G ≃+ H) ↔
    ∀ α : Ordinal, ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  constructor
  · exact ulm_theorem_forward (p := p)
  · exact ulm_theorem_backward (p := p) hGred hHred

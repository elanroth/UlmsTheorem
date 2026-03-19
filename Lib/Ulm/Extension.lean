import Lib.Ulm.Pure

/-!
# Extension lemmas for Ulm's theorem

This file contains the one-generator extension interface used in the hard
direction of Ulm's theorem.
-/

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

/-- Socle-step extension of a height-preserving partial map. -/
lemma socle_extend
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal, ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    {A : AddSubgroup G} (hA : IsPure p A) (hAfg : A.FG)
    {B : AddSubgroup H} (hB : IsPure p B)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    (α : Ordinal) {g : G}
    (hg_socle : g ∈ pSocleAt p α (G := G))
    (hg_notin : g ∉ A)
    (hpg_in  : p • g ∈ A) :
    ∃ (A' : AddSubgroup G) (hAA' : A ≤ A') (_ : g ∈ A')
      (h : H) (_ : h ∈ pSocleAt p α (G := H))
      (_ : p • h = (φ ⟨p • g, hpg_in⟩ : H))
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B ≤ B') (_ : h ∈ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  sorry

/-- General extension by one generator. -/
lemma extend_by_one
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal, ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    {A : AddSubgroup G} (hA : IsPure p A) (hAfg : A.FG)
    {B : AddSubgroup H} (hB : IsPure p B)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    (g : G) :
    ∃ (A' : AddSubgroup G) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  sorry

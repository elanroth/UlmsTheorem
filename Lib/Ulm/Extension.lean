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

omit hp in
 /-- Trivial extension when the prescribed generator is already in the domain subgroup. -/
lemma extend_by_one_of_mem
    {A : AddSubgroup G}
    {B : AddSubgroup H} (hB : IsPure p B)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {g : G} (hg : g ∈ A) :
    ∃ (A' : AddSubgroup G) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  refine ⟨A, le_rfl, hg, B, hB, le_rfl, φ, hφ, ?_⟩
  intro a
  rfl

omit hp in
/-- Trivial finite-stage extension when the prescribed generator is already in the domain subgroup. -/
lemma extend_by_one_fg_of_mem
    {A : AddSubgroup G} (hA : IsPure p A) (hAfg : A.FG)
    {B : AddSubgroup H} (hB : IsPure p B) (hBfg : B.FG)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {g : G} (hg : g ∈ A) :
    ∃ (A' : AddSubgroup G) (_ : IsPure p A') (_ : A'.FG) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B'.FG) (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  refine ⟨A, hA, hAfg, le_rfl, hg, B, hB, hBfg, le_rfl, φ, hφ, ?_⟩
  intro a
  rfl

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
  by_cases hg : g ∈ A
  · exact extend_by_one_of_mem (p := p) hB φ hφ hg
  · sorry

/-- General finite-stage extension by one generator. -/
lemma extend_by_one_fg
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal, ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    {A : AddSubgroup G} (hA : IsPure p A) (hAfg : A.FG)
    {B : AddSubgroup H} (hB : IsPure p B) (hBfg : B.FG)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    (g : G) :
    ∃ (A' : AddSubgroup G) (_ : IsPure p A') (_ : A'.FG) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B'.FG) (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  by_cases hg : g ∈ A
  · exact extend_by_one_fg_of_mem (p := p) hA hAfg hB hBfg φ hφ hg
  · sorry

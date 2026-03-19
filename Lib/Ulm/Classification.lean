import Lib.Ulm.Extension

/-!
# Classification machinery for countable reduced abelian p-groups

This module contains the hard-direction interface for Ulm's theorem:
the back-and-forth construction on finite pure stages and the final
isomorphism-from-invariants statement.
-/

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

/-- A finite stage of the back-and-forth construction. -/
structure BFStep where
  A    : AddSubgroup G
  B    : AddSubgroup H
  hA   : IsPure p A
  hB   : IsPure p B
  hAfg : A.FG
  hBfg : B.FG
  φ    : A →+ B
  hφ   : IsHeightPresOn p φ

/-- The initial empty stage of the back-and-forth construction. -/
def BFStep.init : BFStep p (G := G) (H := H) where
  A    := ⊥
  B    := ⊥
  hA   := IsPure_bot p
  hB   := IsPure_bot p
  hAfg := ⟨∅, by simp⟩
  hBfg := ⟨∅, by simp⟩
  φ    := 0
  hφ   := by
    intro a α
    constructor <;> intro h <;> simp [AddSubgroup.mem_bot.mp a.prop]

omit hp in
/-- Extend a finite stage to cover a prescribed element of `G`. -/
lemma BFStep.forth_of_mem
    (s : BFStep p (G := G) (H := H)) {g : G} (hg : g ∈ s.A) :
    ∃ (s' : BFStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧ ∀ a : s.A, (s'.φ ⟨a.val, hAA a.prop⟩ : H) = s.φ a := by
  refine ⟨s, le_rfl, le_rfl, hg, ?_⟩
  intro a
  rfl

omit hp in
/-- Extend a finite stage to cover a prescribed element of `H` when it is already present. -/
lemma BFStep.back_of_mem
    (s : BFStep p (G := G) (H := H)) {h : H} (hh : h ∈ s.B) :
    ∃ (s' : BFStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      h ∈ s'.B ∧ ∀ a : s.A, (s'.φ ⟨a.val, hAA a.prop⟩ : H) = s.φ a := by
  refine ⟨s, le_rfl, le_rfl, hh, ?_⟩
  intro a
  rfl

/-- Extend a finite stage to cover a prescribed element of `G`. -/
lemma BFStep.forth
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal, ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : BFStep p (G := G) (H := H)) (g : G) :
    ∃ (s' : BFStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧ ∀ a : s.A, (s'.φ ⟨a.val, hAA a.prop⟩ : H) = s.φ a := by
  obtain ⟨A', hA', hAfg', hAA', hgA', B', hB', hBfg', hBB', φ', hφ', hcomp⟩ :=
    extend_by_one_fg (p := p) hG hH hinv s.hA s.hAfg s.hB s.hBfg s.φ s.hφ g
  refine ⟨
    { A := A'
      B := B'
      hA := hA'
      hB := hB'
      hAfg := hAfg'
      hBfg := hBfg'
      φ := φ'
      hφ := hφ' },
    hAA', hBB', hgA', hcomp⟩

/-- Extend a finite stage to cover a prescribed element of `H`. -/
lemma BFStep.back
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal, ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : BFStep p (G := G) (H := H)) (h : H) :
    ∃ (s' : BFStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      h ∈ s'.B ∧ ∀ a : s.A, (s'.φ ⟨a.val, hAA a.prop⟩ : H) = s.φ a := by
  by_cases hh : h ∈ s.B
  · exact s.back_of_mem (p := p) hh
  · sorry

/-- Hard direction of Ulm's theorem: equal Ulm invariants imply isomorphism. -/
lemma iso_of_ulmInvariant_eq
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G)
    (hH : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal, ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) := by
  sorry

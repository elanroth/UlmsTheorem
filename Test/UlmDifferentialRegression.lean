import Lib.Ulm.Theorem

/-!
DIFFERENTIAL TEST OF `ulm_theorem` AGAINST INDEPENDENTLY-KNOWN GROUND TRUTH.

`Z/4 + Z/4` and `Z/2 + Z/8` both have order 16 and are non-isomorphic — a fact
that needs no Ulm theory. Here that non-isomorphism is DERIVED FROM
`ulm_theorem`, by computing the two Ulm invariants at 0 and finding them
different. If the formalized invariant were degenerate, mis-indexed, or blind to
its group argument, it could not separate these two and this file would not
compile.

  Z/4 + Z/4 : socle = {0,2}^2 = 2G exactly, so P_0 = P_1 and f(0) = 0.
  Z/2 + Z/8 : (1,0) is in the socle but not in 2G, so P_0 != P_1 and f(0) != 0.
-/

namespace UlmDifferentialRegression

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

section Witnesses

private lemma reduced_44 : IsReducedPGroup 2 (ZMod 4 × ZMod 4) where
  primary := fun x => ⟨2, by revert x; decide⟩
  reduced := by
    refine ⟨((2 : ℕ) : Ordinal), ?_⟩
    rw [ulmSubgroup_nat]
    ext x
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_setOf_eq, AddSubgroup.mem_bot,
      AddSubsemigroup.mem_mk, AddSubmonoid.mem_mk]
    constructor
    · rintro ⟨y, rfl⟩; revert y; decide
    · rintro rfl; exact ⟨0, by decide⟩

private lemma reduced_28 : IsReducedPGroup 2 (ZMod 2 × ZMod 8) where
  primary := fun x => ⟨3, by revert x; decide⟩
  reduced := by
    refine ⟨((3 : ℕ) : Ordinal), ?_⟩
    rw [ulmSubgroup_nat]
    ext x
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_setOf_eq, AddSubgroup.mem_bot,
      AddSubsemigroup.mem_mk, AddSubmonoid.mem_mk]
    constructor
    · rintro ⟨y, rfl⟩; revert y; decide
    · rintro rfl; exact ⟨0, by decide⟩

end Witnesses

/-- `f(0) = 0` for `Z/4 + Z/4`: its socle is exactly `2G`. -/
theorem ulm_44_zero : ulmInvariant 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4) = 0 := by
  have hsub : pSocleAt 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4)
      ≤ pSocleAt 2 (Order.succ (0 : Ordinal)) (G := ZMod 4 × ZMod 4) := by
    intro x hx
    rw [mem_pSocleAt] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have h1 : Order.succ (0 : Ordinal) = ((1 : ℕ) : Ordinal) := by simp
    rw [h1, ulmSubgroup_nat]
    obtain ⟨hp, -⟩ := hx
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_setOf_eq, AddSubsemigroup.mem_mk,
      AddSubmonoid.mem_mk]
    revert hp
    revert x
    decide
  have htop : ulmDenSubmodule 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4) = ⊤ := by
    ext y
    simp only [Submodule.mem_top, iff_true]
    exact hsub y.2
  haveI hss : Subsingleton (ulmQuotient 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4)) := by
    rw [ulmQuotient, htop]
    infer_instance
  rw [ulmInvariant]
  exact rank_zero_iff.mpr hss

/-- `f(0) != 0` for `Z/2 + Z/8`: `(1,0)` is a socle element outside `2G`. -/
theorem ulm_28_ne_zero : ulmInvariant 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) ≠ 0 := by
  have hmem : ((1 : ZMod 2), (0 : ZMod 8)) ∈ pSocleAt 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) := by
    rw [mem_pSocleAt]
    refine ⟨by decide, ?_⟩
    simp [ulmSubgroup_zero]
  set x : pSocleAt 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) := ⟨_, hmem⟩ with hx
  have hnot : x ∉ ulmDenSubmodule 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) := by
    intro hcon
    have : ((1 : ZMod 2), (0 : ZMod 8))
        ∈ pSocleAt 2 (Order.succ (0 : Ordinal)) (G := ZMod 2 × ZMod 8) := hcon
    rw [mem_pSocleAt] at this
    obtain ⟨-, hin⟩ := this
    have h1 : Order.succ (0 : Ordinal) = ((1 : ℕ) : Ordinal) := by simp
    rw [h1, ulmSubgroup_nat] at hin
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_setOf_eq, AddSubsemigroup.mem_mk,
      AddSubmonoid.mem_mk] at hin
    revert hin
    decide
  haveI : Nontrivial (ulmQuotient 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8)) := by
    refine ⟨Submodule.Quotient.mk x, 0, ?_⟩
    simpa [Submodule.Quotient.mk_eq_zero] using hnot
  rw [ulmInvariant]
  exact ne_of_gt rank_pos

/-- **The differential test.** `ulm_theorem` says these two groups are isomorphic
iff their Ulm invariants agree everywhere. They disagree at 0, so the theorem
forbids an isomorphism — and independently, no isomorphism exists. -/
theorem no_iso_44_28 : ¬ Nonempty ((ZMod 4 × ZMod 4) ≃+ (ZMod 2 × ZMod 8)) := by
  intro hiso
  have hall := (ulm_theorem 2 reduced_44 reduced_28).1 hiso
  have h0 := hall 0
  rw [ulm_44_zero] at h0
  exact ulm_28_ne_zero h0.symm

end UlmDifferentialRegression

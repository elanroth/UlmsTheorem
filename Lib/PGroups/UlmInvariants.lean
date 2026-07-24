import Lib.PGroups.Socle

/-!
# Ulm invariants

For a prime p and a reduced abelian p-group G, the **Ulm invariant** at ordinal α is
  f_G(α) = dim_{ℤ/pℤ} (P_α / P_{α+1}),
where `P_α = G[p] ∩ p^α·G = pSocleAt p α`.

We also keep the raw filtration quotient `G_α / G_{α+1}` available as
`layerQuotient` / `layerInvariant`; this is useful auxiliary data, but it is
not the classical Ulm invariant used in Ulm's theorem.

## Main definitions

- `layerQuotient p α G` : the quotient group `(p^α·G) / (p^(α+1)·G)`
- `layerInvariant p α G` : the cardinal rank of `layerQuotient` as a `ℤ/pℤ`-module
- `ulmQuotient p α G` : the quotient group `P_α / P_{α+1}`
- `ulmInvariant p α G` : the cardinal rank of `ulmQuotient` as a `ℤ/pℤ`-module
- `ulmLength p G` : the least ordinal α with `p^α·G = 0`  (exists for reduced groups)

## References
- Fuchs, "Infinite Abelian Groups", Vol. I, Theorem 32.2
- Kaplansky, "Infinite Abelian Groups", Theorem 12
-/

open Ordinal Cardinal

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### The raw filtration quotient `G_α / G_{α+1}` -/

/-- `G_(α+1)` as a subgroup of `G_α`. -/
noncomputable def layerSuccIncl {G : Type*} [AddCommGroup G] (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) →+ ulmSubgroup p α (G := G) := by
  refine AddSubgroup.subtype _ |>.codRestrict _ ?_
  intro x
  exact ulmSubgroup_antitone p (Order.le_succ α) x.property

/-- The quotient `G_α / G_{α+1}`. This is useful auxiliary filtration data, but
it is not the classical Ulm invariant. -/
noncomputable def layerQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (ulmSubgroup p α (G := G)) ⧸
    ((ulmSubgroup p (Order.succ α) (G := G)).comap
      (ulmSubgroup p α (G := G)).subtype)

noncomputable instance {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddCommGroup (layerQuotient p α (G := G)) := by
  unfold layerQuotient
  infer_instance

/-- Every element of `G_α / G_{α+1}` has order `p`. -/
lemma layerQuotient_orderOf_dvd_p {G : Type*} [AddCommGroup G] (α : Ordinal)
    (x : layerQuotient p α (G := G)) : p • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  change QuotientAddGroup.mk'
      ((ulmSubgroup p (Order.succ α) (G := G)).comap (ulmSubgroup p α (G := G)).subtype)
      (p • a) =
    QuotientAddGroup.mk'
      ((ulmSubgroup p (Order.succ α) (G := G)).comap (ulmSubgroup p α (G := G)).subtype)
      0
  have hmem : (p • (a : G)) ∈ ulmSubgroup p (Order.succ α) (G := G) := by
    rw [ulmSubgroup_succ]
    exact ⟨a, a.property, rfl⟩
  apply (QuotientAddGroup.mk'_eq_mk' _).2
  refine ⟨-(p • a), ?_, by simp⟩
  exact (ulmSubgroup p (Order.succ α) (G := G)).neg_mem hmem

noncomputable instance layerQuotient_module {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Module (ZMod p) (layerQuotient p α (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := layerQuotient p α (G := G)) ?_
  intro x
  simpa using layerQuotient_orderOf_dvd_p p α x

/-- The raw filtration-layer rank `dim_{ℤ/pℤ}(G_α / G_{α+1})`. -/
noncomputable def layerInvariant {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (layerQuotient p α (G := G))

/-! ### The classical Ulm quotient `P_α / P_{α+1}` -/

/-- `P_(α+1)` as a `ZMod p`-submodule of `P_α`. -/
noncomputable def ulmDenSubmodule {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (pSocleAt_succ_subgroupOf p α)

/-- The classical Ulm quotient at `α`: `P_α / P_{α+1}`. -/
abbrev ulmQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α

/-- Every element of the classical Ulm quotient has order `p`. -/
lemma ulmQuotient_orderOf_dvd_p {G : Type*} [AddCommGroup G] (α : Ordinal)
    (x : ulmQuotient p α (G := G)) : p • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  have hp0 : p • a = 0 := by
    ext
    simpa using (mem_pSocleAt p α (a : G)).1 a.property |>.1
  change (Submodule.Quotient.mk (p • a) : ulmQuotient p α (G := G)) = 0
  rw [hp0]
  rfl

/-- The classical Ulm invariant `f_G(α) = dim_{ℤ/pℤ}(P_α / P_{α+1})`. -/
noncomputable def ulmInvariant {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (ulmQuotient p α (G := G))

/-! ### Relative, Hill, and overhang invariants -/

section RelativeInvariants

variable {G : Type*} [AddCommGroup G]

/-- The Hill denominator
`P_(α+1) + (S ∩ P_α)`, viewed as a subgroup of `P_α`. -/
noncomputable def hillDen (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α)).comap
    (pSocleAt p α).subtype

/-- The Hill denominator as a `ZMod p`-submodule of `P_α`. -/
noncomputable def hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (hillDen p S α)

/-- Hill's relative socle space
`P_α / (P_(α+1) + (S ∩ P_α))`. -/
abbrev hillQuotient (S : AddSubgroup G) (α : Ordinal) : Type _ :=
  (pSocleAt p α (G := G)) ⧸ hillSubmodule p S α

/-- The Hill invariant
`dim_(ZMod p) P_α / (P_(α+1) + (S ∩ P_α))`. -/
noncomputable def hillInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (hillQuotient p S α)

/-- With no marked subgroup, the Hill invariant is the ordinary Ulm invariant. -/
theorem hillInvariant_bot (α : Ordinal) :
    hillInvariant p (⊥ : AddSubgroup G) α = ulmInvariant p α (G := G) := by
  have hden :
      hillSubmodule p (⊥ : AddSubgroup G) α = ulmDenSubmodule p α := by
    ext x
    simp [hillSubmodule, hillDen, ulmDenSubmodule, pSocleAt_succ_subgroupOf]
  unfold hillInvariant ulmInvariant
  change Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ hillSubmodule p (⊥ : AddSubgroup G) α) =
    Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α)
  rw [hden]

/-- The BCM/Fuchs relative-Ulm denominator
`P_α ∩ (S + G_(α+1))`, viewed inside `P_α`. -/
noncomputable def relativeUlmDen (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))).comap
    (pSocleAt p α).subtype

/-- The relative-Ulm denominator as a `ZMod p`-submodule of `P_α`. -/
noncomputable def relativeUlmSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (relativeUlmDen p S α)

/-- The BCM/Fuchs relative Ulm space
`P_α / (P_α ∩ (S + G_(α+1)))`. -/
abbrev relativeUlmQuotient (S : AddSubgroup G) (α : Ordinal) : Type _ :=
  (pSocleAt p α (G := G)) ⧸ relativeUlmSubmodule p S α

/-- The BCM/Fuchs relative Ulm invariant.

Walker's `u_G^A` uses the Hill quotient defined above instead; keeping the
attributions distinct prevents the two denominators from being conflated. -/
noncomputable def relativeUlmInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (relativeUlmQuotient p S α)

/-- The Hill denominator is contained in the relative-Ulm denominator. -/
lemma hillSubmodule_le_relativeUlmSubmodule (S : AddSubgroup G) (α : Ordinal) :
    hillSubmodule p S α ≤ relativeUlmSubmodule p S α := by
  intro x hx
  change (x : G) ∈ pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
  change (x : G) ∈
    pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α) at hx
  refine ⟨x.property, ?_⟩
  have hle :
      pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α) ≤
        S ⊔ ulmSubgroup p (Order.succ α) := by
    apply sup_le
    · intro y hy
      exact AddSubgroup.mem_sup_right hy.2
    · intro y hy
      exact AddSubgroup.mem_sup_left hy.1
  exact hle hx

/-- The ordinary Ulm denominator `P_(α+1)` is contained in the
relative-Ulm denominator. -/
lemma ulmDenSubmodule_le_relativeUlmSubmodule (S : AddSubgroup G) (α : Ordinal) :
    ulmDenSubmodule p α ≤ relativeUlmSubmodule p S α := by
  intro x hx
  change (x : G) ∈ pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
  change (x : G) ∈ pSocleAt p (Order.succ α) at hx
  exact ⟨x.property, AddSubgroup.mem_sup_right hx.2⟩

/-- The subspace of the ordinary Ulm layer occupied by the marked subgroup `S`. -/
noncomputable def relativeOccupiedSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (ulmQuotient p α (G := G)) :=
  (relativeUlmSubmodule p S α).map (ulmDenSubmodule p α).mkQ

/-- Quotienting the ordinary Ulm layer by its occupied subspace gives the
relative Ulm space. -/
noncomputable def occupiedQuotientEquivRelative (S : AddSubgroup G) (α : Ordinal) :
    (ulmQuotient p α (G := G) ⧸ relativeOccupiedSubmodule p S α) ≃ₗ[ZMod p]
      relativeUlmQuotient p S α :=
  Submodule.quotientQuotientEquivQuotient
    (ulmDenSubmodule p α) (relativeUlmSubmodule p S α)
    (ulmDenSubmodule_le_relativeUlmSubmodule p S α)

/-- The occupied-space equation underlying the Barwise–Eklof room criterion:
`relative room + occupied = the ordinary Ulm invariant`. -/
theorem relativeUlmInvariant_add_occupiedInvariant
    (S : AddSubgroup G) (α : Ordinal) :
    relativeUlmInvariant p S α +
        Module.rank (ZMod p) (relativeOccupiedSubmodule p S α) =
      ulmInvariant p α (G := G) := by
  unfold relativeUlmInvariant ulmInvariant
  rw [← (occupiedQuotientEquivRelative p S α).rank_eq]
  exact Submodule.rank_quotient_add_rank (relativeOccupiedSubmodule p S α)

/-- The BCM overhang, as the kernel subspace inside the Hill quotient.
This ordinal-indexed definition extends BCM's finite-level construction. -/
noncomputable def overhangSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (hillQuotient p S α) :=
  (relativeUlmSubmodule p S α).map (hillSubmodule p S α).mkQ

/-- The dimension of the BCM overhang space. -/
noncomputable def overhangInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (overhangSubmodule (p := p) S α)

/-- The canonical quotient map from the Hill space onto the relative Ulm space. -/
noncomputable def hillToRelative (S : AddSubgroup G) (α : Ordinal) :
    hillQuotient p S α →ₗ[ZMod p] relativeUlmQuotient p S α :=
  Submodule.factor (hillSubmodule_le_relativeUlmSubmodule p S α)

theorem hillToRelative_surjective (S : AddSubgroup G) (α : Ordinal) :
    Function.Surjective (hillToRelative (p := p) S α) := by
  exact Submodule.factor_surjective (hillSubmodule_le_relativeUlmSubmodule p S α)

/-- BCM's exact-sequence dimension equation:
the Hill invariant is the relative Ulm invariant plus the overhang dimension. -/
theorem relativeUlmInvariant_add_overhangInvariant
    (S : AddSubgroup G) (α : Ordinal) :
    relativeUlmInvariant (p := p) S α + overhangInvariant (p := p) S α =
      hillInvariant p S α := by
  unfold relativeUlmInvariant overhangInvariant hillInvariant
  unfold relativeUlmQuotient hillQuotient overhangSubmodule
  rw [← (Submodule.quotientQuotientEquivQuotient
    (hillSubmodule p S α) (relativeUlmSubmodule p S α)
    (hillSubmodule_le_relativeUlmSubmodule p S α)).rank_eq]
  exact Submodule.rank_quotient_add_rank (overhangSubmodule p S α)

end RelativeInvariants

/-! ### Ulm length -/

/-- The Ulm length of a reduced p-group: the least ordinal α at which p^α·G = 0.
    For countable reduced p-groups this is a countable ordinal. -/
noncomputable def ulmLength {G : Type*} [AddCommGroup G] (_hred : IsReducedPGroup p G) :
    Ordinal.{0} :=
  sInf {α : Ordinal.{0} | ulmSubgroup p α (G := G) = ⊥}

namespace ulmLength

variable {G : Type*} [AddCommGroup G] (hred : IsReducedPGroup p G)

omit hp in
/-- The set `{α | p^α·G = 0}` is nonempty for a reduced p-group. -/
lemma exists_zero (hred' : IsReducedPGroup p G) :
    ∃ α : Ordinal.{0}, ulmSubgroup p α (G := G) = ⊥ := by
  exact hred'.reduced

omit hp in
/-- p^(ulmLength)·G = 0. -/
lemma at_ulmLength : ulmSubgroup p (ulmLength p hred) (G := G) = ⊥ :=
  csInf_mem (exists_zero (p := p) (G := G) hred)

/-- Ulm invariants vanish above the Ulm length. -/
lemma inv_zero_of_ge (α : Ordinal) (hα : ulmLength p hred ≤ α) :
    ulmInvariant p α (G := G) = 0 := by
  have hzero : ulmSubgroup p α (G := G) = ⊥ := by
    apply le_bot_iff.mp
    simpa [at_ulmLength (p := p) (hred := hred)] using
      (ulmSubgroup_antitone p hα : ulmSubgroup p α (G := G) ≤
        ulmSubgroup p (ulmLength p hred) (G := G))
  have hpzero : pSocleAt p α (G := G) = ⊥ := by
    rw [pSocleAt, hzero]
    simp
  haveI : Subsingleton (pSocleAt p α (G := G)) := by
    rw [hpzero]
    infer_instance
  haveI : Subsingleton (ulmQuotient p α (G := G)) := by
    refine ⟨?_⟩
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    obtain rfl : a = b := Subsingleton.elim _ _
    rfl
  rw [ulmInvariant]
  exact rank_subsingleton' (R := ZMod p) (M := ulmQuotient p α (G := G))

end ulmLength

/-! ### Ulm sequence as a function ℕ → Cardinal (for successor-length groups) -/

/-- For groups of Ulm length `ω·γ + n`, the tail Ulm invariants are those at
`ω·γ`, `ω·γ+1`, ..., `ω·γ+(n-1)`. -/
noncomputable def tailInvariants {G : Type*} [AddCommGroup G]
    (γ : Ordinal) (n : ℕ) : Fin n → Cardinal :=
  fun k => ulmInvariant p (ω * γ + k.1) (G := G)

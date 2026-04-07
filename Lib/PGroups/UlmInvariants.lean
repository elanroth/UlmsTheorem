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

/-- The classical Ulm quotient at `α`: `P_α / P_{α+1}`. -/
noncomputable def ulmQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (pSocleAt p α (G := G)) ⧸ pSocleAt_succ_subgroupOf p α

noncomputable instance {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddCommGroup (ulmQuotient p α (G := G)) := by
  unfold ulmQuotient
  infer_instance

/-- Every element of the classical Ulm quotient has order `p`. -/
lemma ulmQuotient_orderOf_dvd_p {G : Type*} [AddCommGroup G] (α : Ordinal)
    (x : ulmQuotient p α (G := G)) : p • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  have hp0 : p • a = 0 := by
    ext
    simpa using (mem_pSocleAt p α (a : G)).1 a.property |>.1
  change QuotientAddGroup.mk' (pSocleAt_succ_subgroupOf p α) (p • a) =
    QuotientAddGroup.mk' (pSocleAt_succ_subgroupOf p α) 0
  simpa [hp0]

noncomputable instance ulmQuotient_module {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Module (ZMod p) (ulmQuotient p α (G := G)) := by
  simpa [ulmQuotient] using (pSocleAt_quot_module (p := p) (G := G) α)

/-- The classical Ulm invariant `f_G(α) = dim_{ℤ/pℤ}(P_α / P_{α+1})`. -/
noncomputable def ulmInvariant {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (ulmQuotient p α (G := G))

/-! ### Ulm length -/

/-- The Ulm length of a reduced p-group: the least ordinal α at which p^α·G = 0.
    For countable reduced p-groups this is a countable ordinal. -/
noncomputable def ulmLength {G : Type*} [AddCommGroup G] (_hred : IsReducedPGroup p G) :
    Ordinal :=
  sInf {α | ulmSubgroup p α (G := G) = ⊥}

namespace ulmLength

variable {G : Type*} [AddCommGroup G] (hred : IsReducedPGroup p G)

/-- The set {α | p^α·G = 0} is nonempty for a reduced p-group. -/
lemma exists_zero (hred' : IsReducedPGroup p G) : ∃ α : Ordinal, ulmSubgroup p α (G := G) = ⊥ := by
  refine ⟨ω, ?_⟩
  have homega : ulmSubgroup p ω (G := G) = ⨅ n : ℕ, pPow p (G := G) n := by
    apply le_antisymm
    · refine le_iInf ?_
      intro n
      rw [← ulmSubgroup_nat (p := p) (G := G) n]
      exact ulmSubgroup_antitone p (Ordinal.nat_lt_omega0 n).le
    · intro x hx
      have hxall : ∀ n : ℕ, x ∈ pPow p (G := G) n := by
        simpa only [AddSubgroup.mem_iInf] using hx
      unfold ulmSubgroup
      rw [Ordinal.limitRecOn_limit _ _ _ _ Ordinal.isSuccLimit_omega0]
      simp only [AddSubgroup.mem_iInf]
      intro β hβ
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hβ
      change x ∈ ulmSubgroup p n (G := G)
      simpa [ulmSubgroup_nat (p := p) (G := G)] using hxall n
  rw [homega]
  exact (isReducedPGroup_iff_iInf (p := p) (G := G)).1 hred'

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

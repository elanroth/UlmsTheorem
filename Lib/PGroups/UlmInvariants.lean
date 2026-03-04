import Lib.PGroups.Defs

/-!
# Ulm invariants

For a prime p and a reduced abelian p-group G, the **Ulm invariant** at ordinal α is
  f_G(α) = dim_{ℤ/pℤ} (p^α·G / p^(α+1)·G).

The Ulm invariants completely determine the isomorphism type of G (Ulm's theorem,
proved in `ACM.UlmTheorem`).

## Main definitions

- `ulmQuotient p α G` : the quotient group (p^α·G) / (p^(α+1)·G)
- `ulmInvariant p α G` : the cardinal rank of ulmQuotient as a ℤ/pℤ-module
- `ulmLength p G` : the least ordinal α with p^α·G = 0  (exists for reduced groups)

## References
- Fuchs, "Infinite Abelian Groups", Vol. I, Theorem 32.2
- Kaplansky, "Infinite Abelian Groups", Theorem 12
-/

open Ordinal Cardinal

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### The Ulm quotient -/

/-- p^(α+1)·G as a subgroup of p^α·G (the inclusion needed for the quotient). -/
noncomputable def ulmSuccIncl {G : Type*} [AddCommGroup G] (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) →+ ulmSubgroup p α (G := G) := by
  sorry

/-- The Ulm quotient at α: (p^α·G) / (p^(α+1)·G).
    This is a ℤ/pℤ-module (every element has order p). -/
noncomputable def ulmQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (ulmSubgroup p α (G := G)) ⧸
    ((ulmSubgroup p (Order.succ α) (G := G)).comap
      (ulmSubgroup p α (G := G)).subtype)

instance {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddCommGroup (ulmQuotient p α (G := G)) := by
  unfold ulmQuotient; infer_instance

/-- Every element of the Ulm quotient has order p. -/
lemma ulmQuotient_orderOf_dvd_p {G : Type*} [AddCommGroup G] [IsPGroup p G] (α : Ordinal)
    (x : ulmQuotient p α (G := G)) : p • x = 0 := by
  sorry

/-! ### ulmQuotient as a ℤ/pℤ-module -/

/-- The Ulm quotient is naturally a ℤ/pℤ-module (vector space over the prime field). -/
noncomputable instance ulmQuotient_module {G : Type*} [AddCommGroup G] [IsPGroup p G]
    (α : Ordinal) : Module (ZMod p) (ulmQuotient p α (G := G)) := by
  sorry

/-! ### Ulm invariants -/

/-- The Ulm invariant f_G(α) = dim_{ℤ/pℤ} (p^α·G / p^(α+1)·G). -/
noncomputable def ulmInvariant {G : Type*} [AddCommGroup G] [IsPGroup p G]
    (α : Ordinal) (G := G) : Cardinal :=
  Module.rank (ZMod p) (ulmQuotient p α (G := G))

/-! ### Ulm length -/

/-- The Ulm length of a reduced p-group: the least ordinal α at which p^α·G = 0.
    For countable reduced p-groups this is a countable ordinal. -/
noncomputable def ulmLength {G : Type*} [AddCommGroup G] (hred : IsReducedPGroup p G) :
    Ordinal :=
  sInf {α | ulmSubgroup p α (G := G) = ⊥}

namespace ulmLength

variable {G : Type*} [AddCommGroup G] (hred : IsReducedPGroup p G)

/-- The set {α | p^α·G = 0} is nonempty for a reduced p-group. -/
lemma exists_zero : ∃ α : Ordinal, ulmSubgroup p α (G := G) = ⊥ := by
  sorry

/-- p^(ulmLength)·G = 0. -/
lemma at_ulmLength : ulmSubgroup p (ulmLength p hred) (G := G) = ⊥ :=
  csInf_mem (exists_zero p hred)

/-- Ulm invariants vanish above the Ulm length. -/
lemma inv_zero_of_ge [IsPGroup p G] (α : Ordinal) (hα : ulmLength p hred ≤ α) :
    ulmInvariant p α (G := G) = 0 := by
  sorry

end ulmLength

/-! ### Ulm sequence as a function ℕ → Cardinal (for successor-length groups) -/

/-- For groups of Ulm length ω·γ + n, the "tail" Ulm invariants are those at
    positions ω·γ, ω·γ+1, …, ω·γ+(n-1).  We extract them as a finite sequence. -/
noncomputable def tailInvariants {G : Type*} [AddCommGroup G] [IsPGroup p G]
    (γ : Ordinal) (n : ℕ) : Fin n → Cardinal :=
  fun k => ulmInvariant p (ω * γ + k) (G := G)

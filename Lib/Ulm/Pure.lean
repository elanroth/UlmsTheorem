import Lib.PGroups.Morphisms
import Lib.PGroups.Socle

/-!
# Pure subgroups and height-preserving partial maps

This file contains the basic hard-direction infrastructure for Ulm's theorem:
ordinal height, p-order, purity, and height-preserving maps on subgroups.
-/

open Ordinal

universe u

variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

/-- The ordinal Ulm height of an element. -/
noncomputable def ulmHeight (x : G) : WithTop Ordinal.{0} :=
  ⨆ (α : Ordinal.{0}) (_ : x ∈ ulmSubgroup p α (G := G)), (α : WithTop Ordinal.{0})

/-- Height-preserving map between full groups. -/
def IsHeightPreserving (φ : G →+ H) : Prop :=
  ∀ (x : G) (α : Ordinal.{0}),
    x ∈ ulmSubgroup p α (G := G) ↔ φ x ∈ ulmSubgroup p α (G := H)

/-- Height-preserving map between subgroups `A ≤ G` and `B ≤ H`. -/
def IsHeightPresOn {A : AddSubgroup G} {B : AddSubgroup H} (φ : A →+ B) : Prop :=
  ∀ (a : A) (α : Ordinal.{0}),
    (a : G) ∈ ulmSubgroup p α (G := G) ↔ (φ a : H) ∈ ulmSubgroup p α (G := H)

/-- The `p`-order of an element: the least `n` such that `p^n • x = 0`,
or `⊤` if no such `n` exists. -/
noncomputable def pOrder (x : G) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : p ^ n • x = 0), (n : ℕ∞)

@[simp] lemma pOrder_zero : pOrder p (0 : G) = 0 := by
  apply le_antisymm
  · exact iInf_le_of_le 0 <| iInf_le_of_le (by simp) le_rfl
  · exact bot_le

lemma smul_eq_zero_iff_le_pOrder (x : G) (n : ℕ) :
    p ^ n • x = 0 ↔ pOrder p x ≤ n := by
  constructor
  · intro hx
    exact iInf_le_of_le n <| iInf_le_of_le hx le_rfl
  · intro h
    by_contra hx
    have hlt : (n : ℕ∞) < pOrder p x := by
      rw [pOrder]
      refine (lt_iInf_iff).2 ?_
      refine ⟨(n + 1 : ℕ∞), by
        simpa using (ENat.lt_coe_add_one_iff (m := (n : ℕ∞)) (n := n)).2 le_rfl, ?_⟩
      intro m
      refine le_iInf ?_
      intro hm
      refine WithTop.coe_le_coe.mpr <| Nat.succ_le_of_lt <| Nat.lt_of_not_ge ?_
      intro hmn
      apply hx
      rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
      rw [pow_add, mul_smul]
      calc
        p ^ m • p ^ k • x = p ^ k • (p ^ m • x) := by
          rw [smul_smul, smul_smul, Nat.mul_comm]
        _ = 0 := by simp [hm]
    exact not_lt_of_ge h hlt

lemma pOrder_smul_p (x : G) (hx : 0 < pOrder p x) :
    pOrder p (p • x) = pOrder p x - 1 := by
  cases hox : pOrder p x using ENat.recTopCoe with
  | top =>
      simpa [hox] using show pOrder p (p • x) = ⊤ from by
        by_contra hy
        rcases WithTop.ne_top_iff_exists.mp hy with ⟨n, hn⟩
        have hle : pOrder p (p • x) ≤ n := by
          rw [← hn]
          exact le_rfl
        have hzero : p ^ n • (p • x) = 0 :=
          (smul_eq_zero_iff_le_pOrder (p := p) (x := p • x) n).2 hle
        have hxzero : p ^ (n + 1) • x = 0 := by
          simpa [pow_succ, mul_smul] using hzero
        have hxle : pOrder p x ≤ n + 1 :=
          (smul_eq_zero_iff_le_pOrder (p := p) (x := x) (n + 1)).1 hxzero
        rw [hox] at hxle
        exact (WithTop.not_top_le_coe (n + 1) hxle).elim
  | coe n =>
      cases n with
      | zero =>
          simp [hox] at hx
      | succ n =>
          have hzero' : p ^ (n + 1) • x = 0 := by
            have hxle : pOrder p x ≤ n + 1 := by
              simp [hox]
            exact (smul_eq_zero_iff_le_pOrder (p := p) (x := x) (n + 1)).2 hxle
          have hupper : pOrder p (p • x) ≤ n := by
            have hzero : p ^ n • (p • x) = 0 := by
              simpa [pow_succ, mul_smul] using hzero'
            exact (smul_eq_zero_iff_le_pOrder (p := p) (x := p • x) n).1 hzero
          cases n with
          | zero =>
              exact le_antisymm hupper bot_le
          | succ m =>
              apply le_antisymm hupper
              by_contra hlow
              have hlt : pOrder p (p • x) < m + 1 := lt_of_not_ge hlow
              have hle : pOrder p (p • x) ≤ m := by
                simpa [Nat.succ_eq_add_one] using
                  (ENat.lt_coe_add_one_iff (m := pOrder p (p • x)) (n := m)).1 hlt
              have hzero : p ^ m • (p • x) = 0 :=
                (smul_eq_zero_iff_le_pOrder (p := p) (x := p • x) m).2 hle
              have hxzero : p ^ (m + 1) • x = 0 := by
                simpa [pow_succ, mul_smul] using hzero
              have hxle : pOrder p x ≤ m + 1 :=
                (smul_eq_zero_iff_le_pOrder (p := p) (x := x) (n := m + 1)).1 hxzero
              rw [hox] at hxle
              exact (not_le_of_gt <| by
                simpa using (ENat.lt_coe_add_one_iff (m := (m : ℕ∞)) (n := m)).2 le_rfl) hxle |>.elim

/-- A subgroup is `p`-pure if divisibility by powers of `p` seen in the ambient
group is already witnessed internally. -/
def IsPure (A : AddSubgroup G) : Prop :=
  ∀ (n : ℕ) (x : A), (x : G) ∈ pPow p n (G := G) → x ∈ pPow p n (G := A)

lemma IsPure_bot : IsPure p (⊥ : AddSubgroup G) := by
  intro n x hx
  refine ⟨0, Subsingleton.elim _ _⟩

lemma IsPure_top : IsPure p (⊤ : AddSubgroup G) := by
  intro n x hx
  rcases hx with ⟨y, hy⟩
  refine ⟨⟨y, by simp⟩, ?_⟩
  exact Subtype.ext hy

lemma IsPure.ulmHeight_eq [Fact p.Prime] {A : AddSubgroup G} (hA : IsPure p A) (x : A) :
    ulmHeight p (x : G) = ulmHeight p x (G := A) := by
  sorry

lemma IsPure.map_of_heightPres [Fact p.Prime] {A : AddSubgroup G} (hA : IsPure p A)
    (φ : G →+ H) (_hφ_inj : Function.Injective φ) (hφ : IsHeightPreserving p φ) :
    IsPure p (A.map φ) := by
  intro n x hx
  rcases x.property with ⟨a, haA, hax⟩
  have hx' : φ a ∈ pPow p n (G := H) := by
    simpa [hax] using hx
  rw [← ulmSubgroup_nat (p := p) n] at hx'
  have ha_pow : a ∈ pPow p n (G := G) := by
    rw [← ulmSubgroup_nat (p := p) n]
    exact (hφ a n).mpr hx'
  rcases hA n ⟨a, haA⟩ ha_pow with ⟨b, hb⟩
  refine ⟨⟨φ b, ⟨b, b.property, rfl⟩⟩, ?_⟩
  ext
  have hb' : p ^ n • (b : G) = a := congrArg (fun z : A => (z : G)) hb
  exact (by
    simpa [map_nsmul] using (congrArg φ hb').trans hax)

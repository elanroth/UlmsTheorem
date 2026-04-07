import Lib.Ulm.Pure

/-!
# Extension lemmas for Ulm's theorem

This file contains the one-generator extension interface used in the hard
direction of Ulm's theorem, formulated against the classical invariants
`dim_{ℤ/pℤ}(P_α / P_{α+1})`.
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

/-- Adjoin one element to a subgroup by taking the supremum with its cyclic closure. -/
def adjoinElem (A : AddSubgroup G) (g : G) : AddSubgroup G :=
  A ⊔ AddSubgroup.closure ({g} : Set G)

lemma le_adjoinElem (A : AddSubgroup G) (g : G) : A ≤ adjoinElem A g := by
  exact le_sup_left

lemma mem_adjoinElem_right (A : AddSubgroup G) (g : G) :
    g ∈ adjoinElem A g := by
  exact
    (show AddSubgroup.closure ({g} : Set G) ≤ adjoinElem A g from le_sup_right)
      (AddSubgroup.subset_closure (by simp))

lemma adjoinElem_fg {A : AddSubgroup G} (hAfg : A.FG) (g : G) :
    (adjoinElem A g).FG := by
  classical
  unfold adjoinElem
  refine hAfg.sup ?_
  exact (AddSubgroup.fg_iff _).2 ⟨{g}, rfl, Set.finite_singleton g⟩

lemma adjoinElem_eq_sup_zmultiples (A : AddSubgroup G) (g : G) :
    adjoinElem A g = A ⊔ AddSubgroup.zmultiples g := by
  unfold adjoinElem
  rw [AddSubgroup.zmultiples_eq_closure]

lemma mem_adjoinElem_iff {A : AddSubgroup G} {g x : G} :
    x ∈ adjoinElem A g ↔ ∃ a ∈ A, ∃ n : ℤ, a + n • g = x := by
  rw [adjoinElem_eq_sup_zmultiples]
  constructor
  · intro hx
    rcases (AddSubgroup.mem_sup).1 hx with ⟨a, ha, z, hz, hsum⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hz with ⟨n, rfl⟩
    exact ⟨a, ha, n, hsum⟩
  · rintro ⟨a, ha, n, rfl⟩
    exact AddSubgroup.add_mem_sup ha <| AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩

lemma socle_extend_build_map
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) {h : H}
    (hpg_in : p • g ∈ A)
    (hrel : p • h = (φ ⟨p • g, hpg_in⟩ : H)) :
    ∃ φ' : adjoinElem A g →+ (⊤ : AddSubgroup H),
      (∀ a : A, (φ' ⟨a, le_adjoinElem (A := A) (g := g) a.prop⟩ : H) = φ a) ∧
      (φ' ⟨g, mem_adjoinElem_right (A := A) g⟩ : H) = h := by
  let ψ : A × ℤ →+ adjoinElem A g :=
    { toFun := fun z =>
        ⟨(z.1 : G) + z.2 • g, (mem_adjoinElem_iff (A := A) (g := g)).2 ⟨z.1, z.1.prop, z.2, rfl⟩⟩
      map_zero' := by
        ext
        simp
      map_add' := by
        intro x y
        ext
        simp [add_assoc, add_left_comm, add_zsmul] }
  have hψ_surj : Function.Surjective ψ := by
    intro x
    rcases (mem_adjoinElem_iff (A := A) (g := g) (x := (x : G))).1 x.prop with ⟨a, ha, n, hn⟩
    refine ⟨(⟨a, ha⟩, n), ?_⟩
    ext
    exact hn
  let χ : A × ℤ →+ H :=
    { toFun := fun z => (φ z.1 : H) + z.2 • h
      map_zero' := by simp
      map_add' := by
        intro x y
        simp [add_assoc, add_left_comm, add_comm, add_zsmul] }
  have hker : ψ.ker ≤ χ.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker] at hz ⊢
    have hz0 : ((z.1 : G) + z.2 • g : G) = 0 := by
      exact congrArg (fun t : adjoinElem A g => (t : G)) hz
    have hzA : z.2 • g ∈ A := by
      have hzA' : z.2 • g = -((z.1 : A) : G) := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [add_comm] using hz0
      rw [hzA']
      exact A.neg_mem z.1.prop
    have hp_dvd : (p : ℤ) ∣ z.2 := by
      by_contra hp_dvd
      have hcop_nat : Nat.Coprime p z.2.natAbs := by
        refine (Nat.Prime.coprime_iff_not_dvd Fact.out).2 ?_
        intro hdiv
        exact hp_dvd (Int.natCast_dvd.2 hdiv)
      have hcop : z.2.gcd ↑p = 1 := by
        rw [Int.gcd_eq_natAbs]
        simpa [Nat.gcd_comm] using hcop_nat.gcd_eq_one
      have hbez : (1 : ℤ) = z.2 * z.2.gcdA ↑p + ↑p * z.2.gcdB ↑p := by
        simpa [hcop] using (Int.gcd_eq_gcd_ab z.2 p)
      have hg_mem : g ∈ A := by
        have hbez' : (1 : ℤ) = z.2.gcdA ↑p * z.2 + z.2.gcdB ↑p * p := by
          simpa [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using hbez
        have hg_expr : g =
            z.2.gcdA ↑p • (z.2 • g) + z.2.gcdB ↑p • ((p : ℤ) • g) := by
          calc
            g = (1 : ℤ) • g := by simp
            _ = (z.2.gcdA ↑p * z.2 + z.2.gcdB ↑p * p) • g := by rw [hbez']
            _ = z.2.gcdA ↑p • (z.2 • g) + z.2.gcdB ↑p • ((p : ℤ) • g) := by
              simp [add_zsmul, mul_zsmul]
        rw [hg_expr]
        exact A.add_mem (A.zsmul_mem hzA _) (A.zsmul_mem (by simpa using hpg_in) _)
      exact hg_notin hg_mem
    rcases hp_dvd with ⟨k, hk⟩
    have hzA0 : z.1 + k • ⟨p • g, hpg_in⟩ = 0 := by
      apply Subtype.ext
      simpa [hk, mul_zsmul, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using hz0
    calc
      χ z = (φ z.1 : H) + ((p : ℤ) * k) • h := by
        simp [χ, hk]
      _ = (φ z.1 : H) + k • (p • h) := by
        simp [mul_zsmul, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      _ = (φ z.1 : H) + k • (φ ⟨p • g, hpg_in⟩ : H) := by rw [hrel]
      _ = (φ (z.1 + k • ⟨p • g, hpg_in⟩) : H) := by
        simp [map_add, map_zsmul]
      _ = 0 := by simp [hzA0]
  let φ0 : adjoinElem A g →+ H :=
    ψ.liftOfSurjective hψ_surj ⟨χ, hker⟩
  refine ⟨φ0.codRestrict ⊤ (by intro x; simp), ?_, ?_⟩
  · intro a
    have hψa : ψ (a, 0) = ⟨(a : G), le_adjoinElem (A := A) (g := g) a.prop⟩ := by
      ext
      simp [ψ]
    change φ0 ⟨(a : G), le_adjoinElem (A := A) (g := g) a.prop⟩ = φ a
    rw [← hψa]
    have hcomp :
        φ0 (ψ (a, 0)) = χ (a, 0) := by
      simpa [φ0] using
        (AddMonoidHom.liftOfRightInverse_comp_apply
          (f := ψ)
          (f_inv := Function.surjInv hψ_surj)
          (hf := Function.rightInverse_surjInv hψ_surj)
          (g := ⟨χ, hker⟩)
          (x := (a, 0)))
    simpa [χ] using hcomp
  ·
    have hψg : ψ (0, 1) = ⟨g, mem_adjoinElem_right (A := A) g⟩ := by
      ext
      simp [ψ]
    change φ0 ⟨g, mem_adjoinElem_right (A := A) g⟩ = h
    rw [← hψg]
    have hcomp :
        φ0 (ψ (0, 1)) = χ (0, 1) := by
      simpa [φ0] using
        (AddMonoidHom.liftOfRightInverse_comp_apply
          (f := ψ)
          (f_inv := Function.surjInv hψ_surj)
          (hf := Function.rightInverse_surjInv hψ_surj)
          (g := ⟨χ, hker⟩)
          (x := (0, 1)))
    simpa [χ] using hcomp

lemma dvd_of_zsmul_mem_of_not_mem
    {A : AddSubgroup G} {g : G}
    (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    (k : ℤ) (hk : k • g ∈ A) : (↑p : ℤ) ∣ k := by
  let qg : G ⧸ A := QuotientAddGroup.mk g
  have hkq : k • qg = 0 := by
    change QuotientAddGroup.mk (k • g) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact hk
  have hpq : p • qg = 0 := by
    change QuotientAddGroup.mk (p • g) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact hpg_in
  have hq_ne : qg ≠ 0 := by
    intro hq
    apply hg_notin
    rw [QuotientAddGroup.eq_zero_iff] at hq
    exact hq
  have horder_dvd : addOrderOf qg ∣ p := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    simpa using hpq
  have horder_eq : addOrderOf qg = p := by
    rw [Nat.dvd_prime hp.1] at horder_dvd
    rcases horder_dvd with horder_one | horder_eq
    · exfalso
      apply hq_ne
      have hzero : (1 : ℕ) • qg = 0 := by
        rw [← horder_one]
        exact addOrderOf_nsmul_eq_zero qg
      simpa using hzero
    · exact horder_eq
  exact horder_eq ▸ addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkq

lemma phi_zsmul_eq_zsmul_h
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    {h : H} (hh_eq : p • h = (↑(φ ⟨p • g, hpg_in⟩) : H))
    (k : ℤ) (hk : k • g ∈ A) :
    (↑(φ ⟨k • g, hk⟩) : H) = k • h := by
  obtain ⟨m, hm⟩ := dvd_of_zsmul_mem_of_not_mem (p := p) hg_notin hpg_in k hk
  calc
    (↑(φ ⟨k • g, hk⟩) : H)
        = (↑(φ ⟨m • (p • g), by
              simpa [hm, mul_zsmul, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using hk⟩) : H) := by
            congr 2
            simpa [hm, mul_zsmul, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
    _ = m • (↑(φ ⟨p • g, hpg_in⟩) : H) := by
          have hmap :
              φ ⟨m • (p • g), by
                exact A.zsmul_mem hpg_in m⟩ = m • φ ⟨p • g, hpg_in⟩ := by
            exact φ.map_zsmul ⟨p • g, hpg_in⟩ m
          exact congrArg Subtype.val hmap
    _ = m • (p • h) := by
          rw [← hh_eq]
    _ = k • h := by
          simpa [hm, mul_zsmul, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]

lemma extend_well_defined
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    {h : H} (hh_eq : p • h = (↑(φ ⟨p • g, hpg_in⟩) : H))
    {a₁ a₂ : G} {n₁ n₂ : ℤ} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (heq : a₁ + n₁ • g = a₂ + n₂ • g) :
    (↑(φ ⟨a₁, ha₁⟩) : H) + n₁ • h = (↑(φ ⟨a₂, ha₂⟩) : H) + n₂ • h := by
  have hrepr' : a₁ - a₂ = n₂ • g - n₁ • g := by
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm, add_left_comm, add_assoc] using heq)
  have hrepr : a₁ - a₂ = (n₂ - n₁) • g := by
    simpa [sub_eq_add_neg, add_zsmul] using hrepr'
  have hkg : (n₂ - n₁) • g ∈ A := by
    rw [← hrepr]
    exact A.sub_mem ha₁ ha₂
  have hphi :
      (φ ⟨(n₂ - n₁) • g, hkg⟩ : H) = (n₂ - n₁) • h := by
    exact phi_zsmul_eq_zsmul_h (p := p) φ hg_notin hpg_in hh_eq (n₂ - n₁) hkg
  have hsub :
      (φ ⟨a₁ - a₂, A.sub_mem ha₁ ha₂⟩ : H) = (n₂ - n₁) • h := by
    have hsame :
        (⟨a₁ - a₂, A.sub_mem ha₁ ha₂⟩ : A) = ⟨(n₂ - n₁) • g, hkg⟩ := by
      apply Subtype.ext
      exact hrepr
    simpa [hsame] using hphi
  have hmap_sub :
      (φ ⟨a₁ - a₂, A.sub_mem ha₁ ha₂⟩ : H) =
        (φ ⟨a₁, ha₁⟩ : H) - (φ ⟨a₂, ha₂⟩ : H) := by
    exact congrArg (fun z : B => (z : H)) (φ.map_sub ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩)
  have hdiff :
      (φ ⟨a₁, ha₁⟩ : H) - (φ ⟨a₂, ha₂⟩ : H) = (n₂ - n₁) • h := by
    exact hmap_sub.symm.trans hsub
  have hsum :
      (φ ⟨a₁, ha₁⟩ : H) = (n₂ - n₁) • h + (φ ⟨a₂, ha₂⟩ : H) := by
    rwa [sub_eq_iff_eq_add] at hdiff
  calc
    (↑(φ ⟨a₁, ha₁⟩) : H) + n₁ • h = ((n₂ - n₁) • h + (φ ⟨a₂, ha₂⟩ : H)) + n₁ • h := by
      rw [hsum]
    _ = (↑(φ ⟨a₂, ha₂⟩) : H) + ((n₂ - n₁) • h + n₁ • h) := by
      abel
    _ = (↑(φ ⟨a₂, ha₂⟩) : H) + ((n₂ - n₁ + n₁) • h) := by
      rw [← add_zsmul]
    _ = (↑(φ ⟨a₂, ha₂⟩) : H) + n₂ • h := by
      congr 1
      abel

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

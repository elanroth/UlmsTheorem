import Lib.Basic

/-!
# Reduced abelian p-groups: core definitions

## References
- Fuchs, "Infinite Abelian Groups", Vol. I, §27–30
- Kaplansky, "Infinite Abelian Groups", §§4–5
-/

open Ordinal

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Natural-number Ulm subgroups -/

/-- p^n·G = { p^n • y | y : G }. -/
def pPow {G : Type*} [AddCommGroup G] (n : ℕ) : AddSubgroup G where
  carrier   := {x | ∃ y : G, p ^ n • y = x}
  zero_mem' := ⟨0, by simp⟩
  add_mem'  := by
    rintro a b ⟨ya, rfl⟩ ⟨yb, rfl⟩
    exact ⟨ya + yb, smul_add (p ^ n) ya yb⟩
  neg_mem'  := by
    rintro a ⟨y, rfl⟩
    exact ⟨-y, smul_neg (p ^ n) y⟩

section PowLemmas

set_option linter.unusedSectionVars false

variable {G : Type*} [AddCommGroup G]

@[simp] lemma pPow_mem_iff (x : G) (n : ℕ) :
    x ∈ pPow p n ↔ ∃ y : G, p ^ n • y = x := Iff.rfl

lemma pPow_zero_eq : pPow p 0 (G := G) = ⊤ := by
  ext x; simp [pow_zero, one_smul]

lemma pPow_succ_le (n : ℕ) : pPow p (n + 1) ≤ pPow p (G := G) n := by
  intro x ⟨y, hy⟩
  exact ⟨p • y, by rw [← hy, pow_succ, mul_smul]⟩

lemma pPow_antitone : Antitone (fun n => pPow p n (G := G)) :=
  antitone_nat_of_succ_le (pPow_succ_le p)

lemma pPow_succ_eq (n : ℕ) :
    (pPow p (G := G) (n + 1) : Set G) = {x | ∃ y ∈ pPow p (G := G) n, p • y = x} := by
  ext x
  simp only [pPow_mem_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨p ^ n • y, ⟨y, rfl⟩, by rw [← hy, smul_smul, mul_comm, ← pow_succ]⟩
  · rintro ⟨z, ⟨w, rfl⟩, hz⟩
    exact ⟨w, by rw [pow_succ, mul_comm, ← smul_smul]; exact hz⟩

end PowLemmas

/-! ### p-image of a subgroup -/

/-- { p • y | y ∈ H } as a subgroup of G. -/
def pImage {G : Type*} [AddCommGroup G] (H : AddSubgroup G) : AddSubgroup G where
  carrier   := {x | ∃ y ∈ H, p • y = x}
  zero_mem' := ⟨0, H.zero_mem, by simp⟩
  add_mem'  := by
    rintro a b ⟨ya, hya, rfl⟩ ⟨yb, hyb, rfl⟩
    exact ⟨ya + yb, H.add_mem hya hyb, smul_add p ya yb⟩
  neg_mem'  := by
    rintro a ⟨y, hy, rfl⟩
    exact ⟨-y, H.neg_mem hy, smul_neg p y⟩

section PImageLemmas

set_option linter.unusedSectionVars false

variable {G : Type*} [AddCommGroup G]

@[simp] lemma mem_pImage (H : AddSubgroup G) (x : G) :
    x ∈ pImage p H ↔ ∃ y ∈ H, p • y = x := Iff.rfl

lemma pImage_pPow (n : ℕ) :
    pImage p (pPow p n (G := G)) = pPow p (n + 1) := by
  ext x
  simp only [mem_pImage, pPow_mem_iff]
  constructor
  · rintro ⟨y, ⟨z, hz⟩, hpy⟩
    exact ⟨z, by rw [← hpy, ← hz, pow_succ, mul_smul, smul_comm]⟩
  · rintro ⟨y, hy⟩
    exact ⟨p ^ n • y, ⟨y, rfl⟩, by rw [← hy, pow_succ, mul_smul, smul_comm]⟩

end PImageLemmas

/-! ### Ordinal Ulm subgroups -/

/-- p^α·G by transfinite recursion:
    p^0·G = G, p^(α+1)·G = {p•x | x ∈ p^α·G}, p^λ·G = ⋂_{β<λ} p^β·G. -/
noncomputable def ulmSubgroup {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddSubgroup G :=
  α.limitRecOn
    ⊤
    (fun _β Hβ => pImage p Hβ)
    (fun o _ho IH => ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)

section UlmSubgroupLemmas

set_option linter.unusedSectionVars false

variable {G : Type*} [AddCommGroup G]

@[simp] lemma ulmSubgroup_zero : ulmSubgroup p (0 : Ordinal) (G := G) = ⊤ := by
  sorry

lemma ulmSubgroup_succ (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) = pImage p (ulmSubgroup p α) := by
  sorry

lemma ulmSubgroup_antitone : Antitone (fun α => ulmSubgroup p α (G := G)) := by
  sorry

lemma ulmSubgroup_nat (n : ℕ) : ulmSubgroup p (n : Ordinal) (G := G) = pPow p n := by
  sorry

end UlmSubgroupLemmas

/-! ### Reduced groups -/

/-- G is reduced if every infinitely p-divisible element is 0. -/
def IsReducedPGroup (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, (∀ n : ℕ, ∃ y : G, p ^ n • y = x) → x = 0

section ReducedLemmas

set_option linter.unusedSectionVars false

variable {G : Type*} [AddCommGroup G]

/-- G is reduced iff ⨅ n : ℕ, pPow p n = ⊥. -/
lemma isReducedPGroup_iff_iInf :
    IsReducedPGroup p G ↔ (⨅ n : ℕ, pPow p (G := G) n) = ⊥ := by
  constructor
  · intro hred
    ext x
    simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_bot]
    exact ⟨fun h => hred x (fun n => (pPow_mem_iff p x n).mp (h n)),
           fun h n => h ▸ (pPow p (G := G) n).zero_mem⟩
  · intro h x hx
    have hmem : x ∈ ⨅ n : ℕ, pPow p (G := G) n := by
      simp only [AddSubgroup.mem_iInf]
      intro n; exact (pPow_mem_iff p x n).mpr (hx n)
    rw [h] at hmem; exact AddSubgroup.mem_bot.mp hmem

end ReducedLemmas

/-! ### p-height -/

/-- The p-height of x: sup { n : ℕ | ∃ y, p^n•y = x }, with ⊤ if infinitely divisible. -/
noncomputable def pHeight {G : Type*} [AddCommGroup G] (x : G) : ℕ∞ :=
  sSup (WithTop.some '' {n : ℕ | ∃ y : G, p ^ n • y = x})

section HeightLemmas

set_option linter.unusedSectionVars false

variable {G : Type*} [AddCommGroup G]

/-- x has height ≥ n iff x ∈ p^n·G. -/
lemma pHeight_ge_iff (x : G) (n : ℕ) :
    (n : ℕ∞) ≤ pHeight p x ↔ ∃ y : G, p ^ n • y = x := by
  constructor
  · intro h
    contrapose! h
    refine' lt_of_le_of_lt (csSup_le _ _) _
    exact ↑(n - 1)
    · exact ⟨_, ⟨0, ⟨x, by simp +decide⟩, rfl⟩⟩
    · rintro _ ⟨m, ⟨y, hy⟩, rfl⟩
      exact WithTop.coe_le_coe.mpr (Nat.le_sub_one_of_lt (lt_of_not_ge fun hnm =>
        h (p ^ (m - n) • y) <| by rw [← MulAction.mul_smul, ← pow_add, Nat.add_sub_of_le hnm, hy]))
    · rcases n with (_ | n) <;> simp_all +decide
      exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self _)
  · intro ⟨y, hy⟩
    apply le_sSup
    exact ⟨n, ⟨y, hy⟩, rfl⟩

lemma pHeight_ge_iff_mem (x : G) (n : ℕ) :
    (n : ℕ∞) ≤ pHeight p x ↔ x ∈ pPow p n := by
  rw [pHeight_ge_iff, pPow_mem_iff]

/-- If x, y have height ≥ n then x + y has height ≥ n. -/
lemma pHeight_add_ge (x y : G) (n : ℕ)
    (hx : (n : ℕ∞) ≤ pHeight p x) (hy : (n : ℕ∞) ≤ pHeight p y) :
    (n : ℕ∞) ≤ pHeight p (x + y) := by
  rw [pHeight_ge_iff] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by rw [smul_add, ha, hb]⟩

/-- 0 has height ⊤. -/
@[simp] lemma pHeight_zero : pHeight p (0 : G) = ⊤ := by
  -- {n | ∃ y, p^n • y = 0} = ℕ (take y = 0), so sSup of its image is ⊤.
  sorry

lemma pHeight_add_ge_min (x y : G) :
    min (pHeight p x) (pHeight p y) ≤ pHeight p (x + y) := by
  by_contra! h_contra
  obtain ⟨n, hn⟩ : ∃ n : ℕ, pHeight p (x + y) < n ∧ n ≤ pHeight p x ∧ n ≤ pHeight p y := by
    by_cases hx : pHeight p x = ⊤ <;> by_cases hy : pHeight p y = ⊤ <;>
      simp_all +decide [lt_top_iff_ne_top]
    · exact?
    · cases' h : pHeight p y with n <;> aesop
    · cases h : pHeight p x <;> aesop
    · cases' h : pHeight p x with n hn; cases' h' : pHeight p y with n' hn'; aesop
      · contradiction
      · cases' h' : pHeight p y with n' hn'; aesop
        cases le_total n n' <;> aesop
  have hxn : ∃ y' : G, p ^ n • y' = x := (pHeight_ge_iff p x n).mp hn.2.1
  have hyn : ∃ y' : G, p ^ n • y' = y := (pHeight_ge_iff p y n).mp hn.2.2
  exact hn.1.not_le ((pHeight_ge_iff p (x + y) n).mpr
    ⟨hxn.choose + hyn.choose, by rw [smul_add, hxn.choose_spec, hyn.choose_spec]⟩)

lemma pHeight_add_eq_min_of_ne (x y : G) (h : pHeight p x ≠ pHeight p y) :
    pHeight p (x + y) = min (pHeight p x) (pHeight p y) := by
  suffices h_ind : ∀ m n : ℕ, m < n → ∀ x y : G,
      pHeight p x = m → pHeight p y = n → pHeight p (x + y) = m by
    cases' lt_or_gt_of_ne h with h h <;> simp_all +decide [min_eq_left_of_lt]
    · cases' eq_or_ne (pHeight p x) ⊤ with hx hx <;>
        cases' eq_or_ne (pHeight p y) ⊤ with hy hy <;>
        simp_all +decide [lt_top_iff_ne_top]
      · have hy_inf : ∀ n : ℕ, ∃ z : G, p ^ n • z = y := fun n => by
          have h_le : (n : ℕ∞) ≤ pHeight p y := by aesop
          exact (pHeight_ge_iff p y n).mp h_le
        have h_ge : pHeight p (x + y) ≥ pHeight p x := by
          have h_ge : ∀ n : ℕ, (n : ℕ∞) ≤ pHeight p x → (n : ℕ∞) ≤ pHeight p (x + y) := by
            intro n hn
            obtain ⟨z, hz⟩ := (pHeight_ge_iff p x n).mp hn
            obtain ⟨w, hw⟩ := hy_inf n
            exact (pHeight_ge_iff p (x + y) n).mpr ⟨z + w, by rw [smul_add, hz, hw]⟩
          exact?
        refine' le_antisymm _ h_ge
        refine' csSup_le _ _ <;> norm_num
        · exact ⟨0, ⟨x + y, by simp +decide⟩⟩
        · rintro b n z hz rfl
          exact (pHeight_ge_iff p x n).mpr (by
            obtain ⟨w, hw⟩ := hy_inf n
            use z - w; simp +decide [hw, hz, smul_sub])
      · cases' x : pHeight p x with m <;> cases' y : pHeight p y with n <;> aesop
    · cases' h : pHeight p x with m <;> cases' h' : pHeight p y with n <;>
        simp_all +decide [add_comm]
      · have hx_inf : ∀ n : ℕ, ∃ z : G, p ^ n • z = x := fun n => by
          have := h ▸ pHeight_ge_iff p x n; aesop
        have h_ge_n : (n : ℕ∞) ≤ pHeight p (x + y) := by
          obtain ⟨z, hz⟩ := hx_inf n
          obtain ⟨w, hw⟩ := (pHeight_ge_iff p y n).mp h'.ge
          exact (pHeight_ge_iff p (x + y) n).mpr ⟨z + w, by rw [smul_add, hz, hw]⟩
        refine' le_antisymm _ h_ge_n
        refine' csSup_le _ _ <;> norm_num
        · exact ⟨0, ⟨x + y, by simp +decide⟩⟩
        · rintro _ m z hz rfl; contrapose! hz; simp_all +decide [pHeight_ge_iff]
          intro H
          have := pHeight_ge_iff p y m; simp_all +decide [pHeight_ge_iff]
          obtain ⟨w, hw⟩ := hx_inf m
          obtain ⟨v, hv⟩ := this.mpr ⟨z - w, by simp +decide [hw, H, smul_sub]⟩
          linarith
          exact hz.not_le (Nat.le_trans ‹_› (Nat.le_succ _))
      · rw [min_eq_right (mod_cast le_of_lt ‹_›), add_comm, h_ind _ _ ‹_› _ _ h' h]
  intros m n mn x y hx hy
  have h_le : pHeight p (x + y) ≥ m :=
    pHeight_add_ge p x y m (hx.ge) (hy.symm ▸ mod_cast mn.le)
  have h_lt : pHeight p (x + y) < n := by
    by_contra h_contra
    have ⟨z, hz⟩ := (pHeight_ge_iff p (x + y) n).mp (le_of_not_gt h_contra)
    have ⟨w, hw⟩ : ∃ w : G, p ^ n • w = x := by
      have ⟨w, hw⟩ : ∃ w : G, p ^ n • w = y := by
        have := pHeight_ge_iff p y n; aesop
      exact ⟨z - w, by simp_all +decide [smul_sub]⟩
    have h_contra'' : pHeight p x ≥ n := (pHeight_ge_iff p x n).mpr ⟨w, hw⟩
    exact absurd h_contra'' (by rw [hx]; exact mod_cast mn.not_le)
  have h_eq : pHeight p (x + y) = m := by
    by_contra h_contra
    have h_gt : pHeight p (x + y) > m := lt_of_le_of_ne h_le (Ne.symm h_contra)
    have ⟨z, hz⟩ : ∃ z : G, p ^ (m + 1) • z = x + y := by
      have h_div : (m + 1 : ℕ∞) ≤ pHeight p (x + y) := by exact?
      exact (pHeight_ge_iff p (x + y) (m + 1)).mp h_div
    have ⟨w, hw⟩ : ∃ w : G, p ^ (m + 1) • w = y := by
      have : pHeight p y ≥ m + 1 := hy.symm ▸ Nat.cast_le.mpr (Nat.succ_le_of_lt mn)
      exact?
    have ⟨v, hv⟩ : ∃ v : G, p ^ (m + 1) • v = x := ⟨z - w, by simp [hz, hw, smul_sub]⟩
    have : pHeight p x ≥ m + 1 := (pHeight_ge_iff p x (m + 1)).mpr ⟨v, hv⟩
    exact absurd this (by rw [hx]; exact mod_cast (Nat.lt_succ_self m).not_le)
  exact h_eq ▸ rfl

end HeightLemmas

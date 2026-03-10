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

/-- The p-height of x: ⊤ if x = 0, otherwise sup { n : ℕ | ∃ y, p^n•y = x }. -/
noncomputable def pHeight {G : Type*} [AddCommGroup G] (x : G) : ℕ∞ :=
  letI : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then ⊤ else sSup (WithTop.some '' {n : ℕ | ∃ y : G, p ^ n • y = x})

section HeightLemmas

set_option linter.unusedSectionVars false

variable {G : Type*} [AddCommGroup G]

/-- 0 has height ⊤. -/
@[simp] lemma pHeight_zero : pHeight p (0 : G) = ⊤ := by
  simp only [pHeight, if_true]

/-- x has height ≥ n iff x ∈ p^n·G. -/
lemma pHeight_ge_iff (x : G) (n : ℕ) :
    (n : ℕ∞) ≤ pHeight p x ↔ ∃ y : G, p ^ n • y = x := by
  by_cases hx : x = 0
  · subst hx
    simp only [pHeight_zero, le_top, true_iff]; exact ⟨0, smul_zero _⟩
  · simp only [pHeight, if_neg hx]
    constructor
    · intro h
      contrapose! h
      refine' lt_of_le_of_lt (csSup_le _ _) _
      exact ↑(n - 1)
      · exact ⟨_, ⟨0, ⟨x, by simp +decide⟩, rfl⟩⟩
      · rintro _ ⟨m, ⟨y, hy⟩, rfl⟩
        exact WithTop.coe_le_coe.mpr (Nat.le_sub_one_of_lt (lt_of_not_ge fun hnm =>
          h (p ^ (m - n) • y) <| by rw [← mul_smul, ← pow_add, Nat.add_sub_of_le hnm, hy]))
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

lemma pHeight_add_ge_min (x y : G) :
    min (pHeight p x) (pHeight p y) ≤ pHeight p (x + y) := by
  by_cases hxy : pHeight p x ≥ pHeight p y
  · have hxy_in_pnG : ∀ n : ℕ, (n : ℕ∞) ≤ pHeight p y → ∃ z : G, p ^ n • z = x + y := by
      intro n hn
      obtain ⟨zx, hzx⟩ := (pHeight_ge_iff p x n).1 (le_trans hn hxy)
      obtain ⟨zy, hzy⟩ := (pHeight_ge_iff p y n).1 hn
      exact ⟨zx + zy, by rw [smul_add, hzx, hzy]⟩
    contrapose! hxy_in_pnG with hxy_not_in_pnG
    simp_all +decide [pHeight_ge_iff]
    obtain ⟨n, hn₁, hn₂⟩ : ∃ n : ℕ, (n : ℕ∞) ≤ pHeight p y ∧ (n : ℕ∞) > pHeight p (x + y) := by
      cases' h : pHeight p y with n
      · cases' h' : pHeight p (x + y) with n'
        · aesop
        · exact ⟨n' + 1, le_top, WithTop.coe_lt_coe.mpr (Nat.lt_succ_self _)⟩
      · aesop
    exact ⟨n, by simpa using (pHeight_ge_iff p y n).1 hn₁,
           fun z hz => (not_le.mpr hn₂) ((pHeight_ge_iff p (x + y) n).2 ⟨z, hz⟩)⟩
  · have h_subadd : ∀ n : ℕ, (n : ℕ∞) ≤ pHeight p x → (n : ℕ∞) ≤ pHeight p (x + y) := fun n hn =>
      pHeight_add_ge p x y n hn (le_trans hn (le_of_not_ge hxy))
    cases h : pHeight p x <;> aesop

lemma pHeight_add_eq_min_of_ne (x y : G) (h : pHeight p x ≠ pHeight p y) :
    pHeight p (x + y) = min (pHeight p x) (pHeight p y) := by
  wlog hx_lt_hy : pHeight p x < pHeight p y generalizing x y
  · rw [add_comm, this y x h.symm (lt_of_le_of_ne (le_of_not_gt hx_lt_hy) h.symm)]
    exact min_comm _ _
  -- First prove h(x+y) ≤ h(x) (the hard direction), then conclude via le_antisymm.
  have hle : pHeight p (x + y) ≤ pHeight p x := by
    -- If h(x+y) > h(x), then x = (x+y) − y has height > h(x), contradiction.
    by_contra hlt
    push_neg at hlt  -- hlt : pHeight p x < pHeight p (x + y)
    -- h(x) is finite since h(x) < h(y) ≤ ⊤
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℕ∞) = pHeight p x :=
      WithTop.ne_top_iff_exists.mp (ne_top_of_lt hx_lt_hy)
    -- k < h(y) and k < h(x+y), so both y and x+y lie in p^(k+1)·G
    have hk_lt_y  : (k : ℕ∞) < pHeight p y       := by rw [hk]; exact hx_lt_hy
    have hk_lt_xy : (k : ℕ∞) < pHeight p (x + y) := by rw [hk]; exact hlt
    -- helper: (k : ℕ∞) < a → (↑(k+1) : ℕ∞) ≤ a
    have succ_le : ∀ a : ℕ∞, (k : ℕ∞) < a → (↑(k + 1) : ℕ∞) ≤ a := fun a ha => by
      rcases a with (_ | m)
      · exact le_top
      · exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp ha))
    obtain ⟨zy,  hzy ⟩ := (pHeight_ge_iff p y       (k + 1)).mp (succ_le _ hk_lt_y)
    obtain ⟨zxy, hzxy⟩ := (pHeight_ge_iff p (x + y) (k + 1)).mp (succ_le _ hk_lt_xy)
    -- x = (x+y) − y ∈ p^(k+1)·G, contradicting h(x) = k
    have hx_mem : (↑(k + 1) : ℕ∞) ≤ pHeight p x :=
      (pHeight_ge_iff p x (k + 1)).mpr ⟨zxy - zy, by rw [smul_sub, hzxy, hzy, add_sub_cancel_right]⟩
    rw [← hk] at hx_mem
    exact absurd (WithTop.coe_le_coe.mp hx_mem) (by omega)
  -- h(x+y) = min(h(x), h(y)): upper bound from hle + transitivity, lower bound from subadditivity.
  exact le_antisymm (le_min hle (le_trans hle hx_lt_hy.le)) (pHeight_add_ge_min p x y)

end HeightLemmas

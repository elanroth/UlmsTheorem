import Lib.PGroups.Subgroups

/-!
# Ordinal Ulm subgroups

This file contains the transfinite Ulm filtration `ulmSubgroup` and its basic
structural lemmas.
-/

open Ordinal

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p^α·G` by transfinite recursion:
`p^0·G = G`, `p^(α+1)·G = {p•x | x ∈ p^α·G}`, and
`p^λ·G = ⋂_{β<λ} p^β·G`. -/
noncomputable def ulmSubgroup {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddSubgroup G :=
  α.limitRecOn
    ⊤
    (fun _β Hβ ↦ pImage p Hβ)
    (fun o _ho IH ↦ ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)

section UlmSubgroupLemmas

set_option linter.unusedSectionVars false

variable {G : Type*} [AddCommGroup G]

@[simp] lemma ulmSubgroup_zero : ulmSubgroup p (0 : Ordinal) (G := G) = ⊤ := by
  rw [ulmSubgroup, Ordinal.limitRecOn_zero]

lemma ulmSubgroup_succ (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) = pImage p (ulmSubgroup p α) := by
  rw [ulmSubgroup, Ordinal.limitRecOn_succ, ulmSubgroup]

lemma ulmSubgroup_limit (o : Ordinal) (ho : Order.IsSuccLimit o) :
    ulmSubgroup p o (G := G) = ⨅ (β : Ordinal) (_ : β < o), ulmSubgroup p β := by
  unfold ulmSubgroup
  simpa using
    (Ordinal.limitRecOn_limit o
      (⊤ : AddSubgroup G)
      (fun _β Hβ ↦ pImage p Hβ)
      (fun o _ho IH ↦ ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)
      ho)

@[simp] lemma mem_ulmSubgroup_succ_iff (α : Ordinal) (x : G) :
    x ∈ ulmSubgroup p (Order.succ α) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p • y = x := by
  rw [ulmSubgroup_succ, mem_pImage]

lemma mem_ulmSubgroup_limit_iff {o : Ordinal} (ho : Order.IsSuccLimit o) (x : G) :
    x ∈ ulmSubgroup p o (G := G) ↔ ∀ β < o, x ∈ ulmSubgroup p β := by
  rw [ulmSubgroup_limit (p := p) (G := G) o ho]
  simp only [AddSubgroup.mem_iInf]

lemma ulmSubgroup_antitone : Antitone (fun α ↦ ulmSubgroup p α (G := G)) := by
  let P : Ordinal → Prop := fun β ↦ ∀ α, α ≤ β → ulmSubgroup p β (G := G) ≤ ulmSubgroup p α
  have hP : ∀ β, P β := by
    intro β
    induction β using Ordinal.limitRecOn with
    | zero =>
        intro α hαβ
        have h0 : α = 0 := le_antisymm hαβ bot_le
        simp [h0]
    | succ β ih =>
        intro α hαβ
        have hs : ulmSubgroup p (Order.succ β) (G := G) ≤ ulmSubgroup p β := by
          rw [ulmSubgroup_succ]
          intro x hx
          rcases hx with ⟨y, hy, rfl⟩
          simpa using (ulmSubgroup p β (G := G)).nsmul_mem hy p
        rcases lt_or_eq_of_le hαβ with hlt | rfl
        · exact hs.trans (ih α (Order.le_of_lt_succ hlt))
        · exact le_rfl
    | limit o ho IH =>
        intro α hαβ
        rcases lt_or_eq_of_le hαβ with hlt | rfl
        · simp [ulmSubgroup, Ordinal.limitRecOn_limit, ho]
          exact iInf_le_of_le α (iInf_le _ hlt)
        · exact le_rfl
  intro α β hαβ
  exact hP β α hαβ

lemma ulmSubgroup_nat (n : ℕ) : ulmSubgroup p (n : Ordinal) (G := G) = pPow p n := by
  induction n with
  | zero =>
      rw [show ((0 : ℕ) : Ordinal) = 0 by simp, ulmSubgroup_zero, pPow_zero_eq]
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : Ordinal) = Order.succ (n : Ordinal) by simp]
      rw [ulmSubgroup_succ, ih, pImage_pPow]

lemma mem_ulmSubgroup_nat_iff (n : ℕ) (x : G) :
    x ∈ ulmSubgroup p (n : Ordinal) (G := G) ↔ ∃ y : G, p ^ n • y = x := by
  rw [ulmSubgroup_nat, pPow_mem_iff]

lemma mem_ulmSubgroup_add_nat_iff (α : Ordinal) (n : ℕ) (x : G) :
    x ∈ ulmSubgroup p (α + n) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p ^ n • y = x := by
  induction n generalizing x with
  | zero =>
      simp
  | succ n ih =>
      rw [natCast_succ, add_succ, mem_ulmSubgroup_succ_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases (ih z).1 hz with ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        rw [pow_succ, mul_smul, smul_comm]
      · rintro ⟨y, hy, hxy⟩
        refine ⟨p ^ n • y, (ih _).2 ⟨y, hy, rfl⟩, ?_⟩
        rw [← hxy, pow_succ, mul_smul, smul_comm]

lemma ulmSubgroup_add_nat (α : Ordinal) (n : ℕ) :
    ulmSubgroup p (α + n) (G := G) =
      { x | ∃ y ∈ ulmSubgroup p α (G := G), p ^ n • y = x } := by
  ext x
  exact mem_ulmSubgroup_add_nat_iff (p := p) (G := G) α n x

lemma map_ulmSubgroup_le {H : Type*} [AddCommGroup H] (φ : G →+ H) (α : Ordinal) :
    (ulmSubgroup p α (G := G)).map φ ≤ ulmSubgroup p α (G := H) := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      simp [ulmSubgroup]
  | succ α ih =>
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [ulmSubgroup_succ] at hx ⊢
      rcases hx with ⟨z, hz, rfl⟩
      exact ⟨φ z, ih ⟨z, hz, rfl⟩, by simp⟩
  | limit o ho IH =>
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      simp [ulmSubgroup, Ordinal.limitRecOn_limit, ho] at hx ⊢
      intro β hβ
      exact IH β hβ ⟨x, hx β hβ, rfl⟩

/-- Translating by a multiple of an element already in `G_β` does not change
membership in `G_β`. -/
lemma add_zsmul_mem_iff_of_mem {β : Ordinal.{0}} {x c : G}
    (hx : x ∈ ulmSubgroup p β (G := G)) (n : ℤ) :
    c + n • x ∈ ulmSubgroup p β (G := G) ↔ c ∈ ulmSubgroup p β (G := G) := by
  constructor
  · intro h
    simpa using (ulmSubgroup p β (G := G)).sub_mem h
      ((ulmSubgroup p β (G := G)).zsmul_mem hx n)
  · intro h
    exact (ulmSubgroup p β (G := G)).add_mem h
      ((ulmSubgroup p β (G := G)).zsmul_mem hx n)

end UlmSubgroupLemmas

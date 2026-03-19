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
    (fun _β Hβ => pImage p Hβ)
    (fun o _ho IH => ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)

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
      (fun _β Hβ => pImage p Hβ)
      (fun o _ho IH => ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)
      ho)

@[simp] lemma mem_ulmSubgroup_succ_iff (α : Ordinal) (x : G) :
    x ∈ ulmSubgroup p (Order.succ α) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p • y = x := by
  rw [ulmSubgroup_succ, mem_pImage]

lemma mem_ulmSubgroup_limit_iff {o : Ordinal} (ho : Order.IsSuccLimit o) (x : G) :
    x ∈ ulmSubgroup p o (G := G) ↔ ∀ β < o, x ∈ ulmSubgroup p β := by
  rw [ulmSubgroup_limit (p := p) (G := G) o ho]
  simp only [AddSubgroup.mem_iInf]

lemma ulmSubgroup_antitone : Antitone (fun α => ulmSubgroup p α (G := G)) := by
  let P : Ordinal → Prop := fun β => ∀ α, α ≤ β → ulmSubgroup p β (G := G) ≤ ulmSubgroup p α
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

end UlmSubgroupLemmas

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
  sorry

lemma ulmSubgroup_succ (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) = pImage p (ulmSubgroup p α) := by
  sorry

lemma ulmSubgroup_antitone : Antitone (fun α => ulmSubgroup p α (G := G)) := by
  sorry

lemma ulmSubgroup_nat (n : ℕ) : ulmSubgroup p (n : Ordinal) (G := G) = pPow p n := by
  sorry

end UlmSubgroupLemmas

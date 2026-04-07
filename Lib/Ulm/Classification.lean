import Lib.Ulm.Extension

/-!
# Classification machinery for countable reduced abelian p-groups

This module contains the hard-direction interface for Ulm's theorem:
the back-and-forth construction on finite pure stages and the final
isomorphism-from-invariants statement.
-/

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

/-- A finite stage of the back-and-forth construction. -/
structure BFStep where
  A    : AddSubgroup G
  B    : AddSubgroup H
  hA   : IsPure p A
  hB   : IsPure p B
  hAfg : A.FG
  hBfg : B.FG
  φ    : A →+ B
  hφ   : IsHeightPresOn p φ

/-- The initial empty stage of the back-and-forth construction. -/
def BFStep.init : BFStep p (G := G) (H := H) where
  A    := ⊥
  B    := ⊥
  hA   := IsPure_bot p
  hB   := IsPure_bot p
  hAfg := ⟨∅, by simp⟩
  hBfg := ⟨∅, by simp⟩
  φ    := 0
  hφ   := by
    intro a α
    constructor <;> intro h <;> simp [AddSubgroup.mem_bot.mp a.prop]

omit hp in
/-- Extend a finite stage to cover a prescribed element of `G`. -/
lemma BFStep.forth_of_mem
    (s : BFStep p (G := G) (H := H)) {g : G} (hg : g ∈ s.A) :
    ∃ (s' : BFStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧ ∀ a : s.A, (s'.φ ⟨a.val, hAA a.prop⟩ : H) = s.φ a := by
  refine ⟨s, le_rfl, le_rfl, hg, ?_⟩
  intro a
  rfl

omit hp in
/-- Extend a finite stage to cover a prescribed element of `H` when it is already present. -/
lemma BFStep.back_of_mem
    (s : BFStep p (G := G) (H := H)) {h : H} (hh : h ∈ s.B) :
    ∃ (s' : BFStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      h ∈ s'.B ∧ ∀ a : s.A, (s'.φ ⟨a.val, hAA a.prop⟩ : H) = s.φ a := by
  refine ⟨s, le_rfl, le_rfl, hh, ?_⟩
  intro a
  rfl

lemma BFStep.injective
    (hG : IsReducedPGroup p G) (s : BFStep p (G := G) (H := H)) :
    Function.Injective s.φ :=
  IsHeightPresOn.injective (p := p) hG s.hφ

/-- Extend a finite stage to cover a prescribed element of `G`. -/
lemma BFStep.forth
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal, ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : BFStep p (G := G) (H := H)) (g : G) :
    ∃ (s' : BFStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧ ∀ a : s.A, (s'.φ ⟨a.val, hAA a.prop⟩ : H) = s.φ a := by
  obtain ⟨A', hA', hAfg', hAA', hgA', B', hB', hBfg', hBB', φ', hφ', hcomp⟩ :=
    extend_by_one_fg (p := p) hG hH hinv s.hA s.hAfg s.hB s.hBfg s.φ s.hφ g
  refine ⟨
    { A := A'
      B := B'
      hA := hA'
      hB := hB'
      hAfg := hAfg'
      hBfg := hBfg'
      φ := φ'
      hφ := hφ' },
    hAA', hBB', hgA', hcomp⟩

def rangeInH (s : BFStep p (G := G) (H := H)) : AddSubgroup H :=
  (s.B.subtype.comp s.φ).range

lemma rangeInH_pure (s : BFStep p (G := G) (H := H)) :
    IsPure p (rangeInH p s) := by
  have := IsPure.range_of_heightPresOn (p := p) s.hA s.φ s.hφ
  convert this using 1
  ext x; simp [rangeInH, AddSubgroup.mem_map, AddMonoidHom.mem_range]

lemma rangeInH_fg (s : BFStep p (G := G) (H := H)) :
    (rangeInH p s).FG := by
  have : AddGroup.FG s.A := (AddGroup.fg_iff_addSubgroup_fg s.A).mpr s.hAfg
  exact (AddGroup.fg_iff_addSubgroup_fg _).mp (AddGroup.fg_range (s.B.subtype.comp s.φ))

lemma comp_injective (hG : IsReducedPGroup p G) (s : BFStep p (G := G) (H := H)) :
    Function.Injective (s.B.subtype.comp s.φ) := by
  intro x y hxy; exact BFStep.injective p hG s (Subtype.val_injective hxy)

noncomputable def invOnRange (hG : IsReducedPGroup p G) (s : BFStep p (G := G) (H := H)) :
    rangeInH p s →+ s.A :=
  (AddMonoidHom.ofInjective (comp_injective p hG s)).symm.toAddMonoidHom

lemma invOnRange_spec (hG : IsReducedPGroup p G) (s : BFStep p (G := G) (H := H)) (a : s.A) :
    invOnRange p hG s ⟨(s.B.subtype.comp s.φ) a, ⟨a, rfl⟩⟩ = a :=
  (AddMonoidHom.ofInjective (comp_injective p hG s)).symm_apply_apply a

lemma invOnRange_heightPres (hG : IsReducedPGroup p G) (s : BFStep p (G := G) (H := H)) :
    IsHeightPresOn p (invOnRange p hG s) := by
  intro ⟨y, hy⟩ α; rcases hy with ⟨a, rfl⟩
  rw [invOnRange_spec p hG s a]; exact (s.hφ a α).symm

lemma extend_by_list
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal, ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    {C : AddSubgroup H} (hC : IsPure p C) (hCfg : C.FG)
    {A : AddSubgroup G} (hA : IsPure p A) (hAfg : A.FG)
    (ψ : C →+ A) (hψ : IsHeightPresOn p ψ)
    (elems : List H) :
    ∃ (C' : AddSubgroup H) (_ : IsPure p C') (_ : C'.FG) (hCC' : C ≤ C')
      (_ : ∀ e ∈ elems, e ∈ C')
      (A' : AddSubgroup G) (_ : IsPure p A') (_ : A'.FG) (_ : A ≤ A')
      (ψ' : C' →+ A'),
        IsHeightPresOn p ψ' ∧
        ∀ c : C, (ψ' ⟨c.val, hCC' c.prop⟩ : G) = (ψ c : G) := by
  induction elems with
  | nil =>
    exact ⟨C, hC, hCfg, le_rfl, fun _ h => absurd h List.not_mem_nil,
           A, hA, hAfg, le_rfl, ψ, hψ, fun c => rfl⟩
  | cons e es ih =>
    obtain ⟨C₁, hC₁p, hC₁fg, hCC₁, hes₁, A₁, hA₁p, hA₁fg, hAA₁, ψ₁, hψ₁, hcomp₁⟩ := ih
    obtain ⟨C₂, hC₂p, hC₂fg, hC₁C₂, he₂, A₂, hA₂p, hA₂fg, hA₁A₂, ψ₂, hψ₂, hcomp₂⟩ :=
      extend_by_one_fg (G := H) (H := G) (p := p) hH hG
        (fun β => (hinv β).symm) hC₁p hC₁fg hA₁p hA₁fg ψ₁ hψ₁ e
    refine ⟨C₂, hC₂p, hC₂fg, le_trans hCC₁ hC₁C₂, ?_,
            A₂, hA₂p, hA₂fg, le_trans hAA₁ hA₁A₂, ψ₂, hψ₂, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact he₂
      · exact hC₁C₂ (hes₁ x hmem)
    · intro c
      exact (by congr 1 : (ψ₂ ⟨↑c, (le_trans hCC₁ hC₁C₂) c.prop⟩ : G) =
        (ψ₂ ⟨(⟨↑c, hCC₁ c.prop⟩ : C₁).val, hC₁C₂ (⟨↑c, hCC₁ c.prop⟩ : C₁).prop⟩ : G)).trans
        ((hcomp₂ ⟨c.val, hCC₁ c.prop⟩).trans (hcomp₁ c))

/-- The extended map already covers the old domain stage. -/
lemma range_contains_A
    (hG : IsReducedPGroup p G)
    (s : BFStep p (G := G) (H := H))
    {C' : AddSubgroup H} {A' : AddSubgroup G}
    (hCC' : rangeInH p s ≤ C')
    (ψ' : C' →+ A')
    (hψ'comp : ∀ c : rangeInH p s,
      (ψ' ⟨c.val, hCC' c.prop⟩ : G) = (invOnRange p hG s c : G)) :
    s.A ≤ (A'.subtype.comp ψ').range := by
  intro x hx; use ⟨ ( s.B.subtype.comp s.φ ) ⟨ x, hx ⟩, hCC' ⟨ ⟨ x, hx ⟩, rfl ⟩ ⟩ ; simp [ hψ'comp ] ;
  convert hψ'comp ⟨ _, ⟨ ⟨ x, hx ⟩, rfl ⟩ ⟩ using 1;
  exact Eq.symm ( invOnRange_spec p hG s ⟨ x, hx ⟩ ) ▸ rfl

/-- Compatibility of the new inverse map with the previous finite stage. -/
lemma compat_proof
    (hG : IsReducedPGroup p G)
    (s : BFStep p (G := G) (H := H))
    {C' : AddSubgroup H} {A' : AddSubgroup G}
    (hCC' : rangeInH p s ≤ C')
    (ψ' : C' →+ A')
    (hci : Function.Injective (A'.subtype.comp ψ'))
    (hψ'comp : ∀ c : rangeInH p s,
      (ψ' ⟨c.val, hCC' c.prop⟩ : G) = (invOnRange p hG s c : G))
    (hA_le : s.A ≤ (A'.subtype.comp ψ').range)
    (a : s.A) :
    (((AddMonoidHom.ofInjective hci).symm.toAddMonoidHom
      ⟨a.val, hA_le a.prop⟩ : C') : H) = (s.φ a : H) := by
  obtain ⟨ ca, hca ⟩ := hA_le a.2;
  have h_eq : ca = (s.B.subtype.comp s.φ) a := by
    have h_eq : ψ' ⟨(s.B.subtype.comp s.φ) a, hCC' ⟨a, rfl⟩⟩ = ψ' ca := by
      convert hψ'comp ⟨(s.B.subtype.comp s.φ) a, ⟨a, rfl⟩⟩ using 1;
      rw [ invOnRange_spec p hG s a ] ; aesop;
    have := @hci ⟨ ( s.B.subtype.comp s.φ ) a, hCC' ⟨ a, rfl ⟩ ⟩ ca; aesop;
  convert h_eq using 1;
  convert congr_arg Subtype.val ( ( AddMonoidHom.ofInjective hci ).symm_apply_apply ca ) using 1;
  congr! 1;
  exact congr_arg _ ( Subtype.ext hca.symm )

/-- Nontrivial back-step branch when the target element is not already present. -/
lemma BFStep.back_not_mem
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal, ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : BFStep p (G := G) (H := H)) (h : H) (hh : h ∉ s.B) :
    ∃ (s' : BFStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      h ∈ s'.B ∧ ∀ a : s.A, (s'.φ ⟨a.val, hAA a.prop⟩ : H) = s.φ a := by
  rcases s.hBfg with ⟨S, hS⟩
  obtain ⟨C', hC'p, hC'fg, hCC', helems, A', hA'p, hA'fg, hAA', ψ', hψ'hp, hψ'comp⟩ :=
    extend_by_list p hG hH hinv (rangeInH_pure p s) (rangeInH_fg p s)
      s.hA s.hAfg (invOnRange p hG s) (invOnRange_heightPres p hG s) (h :: S.toList)
  have hB_le : s.B ≤ C' := by
    rw [← hS]; exact (AddSubgroup.closure_le C').mpr
      (fun x hx => helems x (List.mem_cons_of_mem _ (Finset.mem_toList.mpr hx)))
  have hψ'_inj := IsHeightPresOn.injective (p := p) hH hψ'hp
  have hci : Function.Injective (A'.subtype.comp ψ') :=
    fun x y hxy => hψ'_inj (Subtype.val_injective hxy)
  have hA_le := range_contains_A p hG s hCC' ψ' hψ'comp
  let φ_new : (A'.subtype.comp ψ').range →+ C' :=
    (AddMonoidHom.ofInjective hci).symm.toAddMonoidHom
  have hφ_hp : IsHeightPresOn p φ_new := by
    intro x α; constructor <;> intro h <;> simp_all +decide [ AddSubgroup.mem_map ] ; (
    -- Since $x$ is in the range of $A'.subtype.comp ψ'$, there exists $y \in C'$ such that $x = (A'.subtype.comp ψ') y$.
    obtain ⟨y, hy⟩ : ∃ y : C', x = (A'.subtype.comp ψ') y := by
      exact ⟨ x.2.choose, x.2.choose_spec.symm ⟩;
    -- Since $x = (A'.subtype.comp ψ') y$, we have $\phi_new x = y$ by definition of $\phi_new$.
    have h_phi_new_x : (φ_new x : H) = (y : H) := by
      have h_phi_new_x : (φ_new x : C') = y := by
        have : x = (AddMonoidHom.ofInjective hci).toAddMonoidHom y := by
          exact Subtype.ext hy
        exact this.symm ▸ by simp +decide [ φ_new ] ;
      generalize_proofs at *; (
      exact congr_arg Subtype.val h_phi_new_x ▸ rfl);
    have := hψ'hp y α; aesop;);
    convert hψ'hp _ _ |>.1 h using 1
    generalize_proofs at *; (
    exact congr_arg Subtype.val ( Eq.symm <| AddEquiv.apply_symm_apply ( AddMonoidHom.ofInjective hci ) _ ) ▸ rfl)
  refine ⟨⟨(A'.subtype.comp ψ').range, C',
           (by have := IsPure.range_of_heightPresOn (p := p) hC'p ψ' hψ'hp; convert this using 1; ext; simp [AddMonoidHom.mem_range]), hC'p,
           (by haveI : AddGroup.FG C' := (AddGroup.fg_iff_addSubgroup_fg C').mpr hC'fg
               exact (AddGroup.fg_iff_addSubgroup_fg _).mp (AddGroup.fg_range _)),
           hC'fg, φ_new, hφ_hp⟩,
          hA_le, hB_le, helems h (@List.mem_cons_self _ h _), ?_⟩
  intro a
  exact compat_proof p hG s hCC' ψ' hci hψ'comp hA_le a

/-- Extend a finite stage to cover a prescribed element of `H`. -/
lemma BFStep.back
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal, ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : BFStep p (G := G) (H := H)) (h : H) :
    ∃ (s' : BFStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      h ∈ s'.B ∧ ∀ a : s.A, (s'.φ ⟨a.val, hAA a.prop⟩ : H) = s.φ a := by
  by_cases hh : h ∈ s.B
  · exact s.back_of_mem (p := p) hh
  · exact s.back_not_mem (p := p) hG hH hinv h hh

/-!
## Isomorphism-from-equivalences back-and-forth assembly

`BFIsoStep` is a finite stage carrying an actual `AddEquiv` (rather than a plain hom).
The chain construction below proves `iso_of_ulmInvariant_eq_of_backAndForth`:
given abstract `hforth`/`hback` hypotheses that supply `BFIsoStep` extensions,
the colimit is an isomorphism.  The connection to the concrete extension machinery
(and hence the proof of `iso_of_ulmInvariant_eq`) still awaits `socle_extend`.
-/

/-- A finite stage carrying a true partial isomorphism. -/
structure BFIsoStep where
  A    : AddSubgroup G
  B    : AddSubgroup H
  hA   : IsPure p A
  hB   : IsPure p B
  hAfg : A.FG
  hBfg : B.FG
  e    : A ≃+ B
  hφ   : IsHeightPresOn p e.toAddMonoidHom

/-- The initial empty stage. -/
private def BFIsoStep.init : BFIsoStep p (G := G) (H := H) where
  A    := ⊥
  B    := ⊥
  hA   := IsPure_bot p
  hB   := IsPure_bot p
  hAfg := ⟨∅, by simp⟩
  hBfg := ⟨∅, by simp⟩
  e    := {
    toFun    := fun a => ⟨0, AddSubgroup.zero_mem _⟩
    invFun   := fun b => ⟨0, AddSubgroup.zero_mem _⟩
    left_inv := fun a => Subtype.ext (by simp [AddSubgroup.mem_bot.mp a.prop])
    right_inv:= fun b => Subtype.ext (by simp [AddSubgroup.mem_bot.mp b.prop])
    map_add' := fun a b => by
      simp [Subtype.ext_iff, AddSubgroup.mem_bot.mp a.prop, AddSubgroup.mem_bot.mp b.prop] }
  hφ   := by
    intro a α
    have ha : (a : G) = 0 := AddSubgroup.mem_bot.mp a.prop
    constructor <;> intro h <;> simp [ha]

/-- Combine one forth step and one back step into a single chain step. -/
private lemma bf_forth_back
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (s : BFIsoStep p (G := G) (H := H)) (g : G) (h : H) :
    ∃ (s' : BFIsoStep p (G := G) (H := H)) (hle : s.A ≤ s'.A),
      s.B ≤ s'.B ∧ g ∈ s'.A ∧ h ∈ s'.B ∧
      ∀ a : s.A, (s'.e ⟨a.val, hle a.prop⟩ : H) = s.e a := by
  obtain ⟨s₁, h₁, h₂, hg₁, h₃⟩ := hforth s g
  obtain ⟨s₂, h₄, h₅, hh₂, h₆⟩ := hback s₁ h
  exact ⟨s₂, h₁.trans h₄, h₂.trans h₅, h₄ hg₁, hh₂,
         fun a => by simpa [h₃ a] using h₆ ⟨a, h₁ a.2⟩⟩

/-- The ℕ-indexed chain of `BFIsoStep`s, covering one element of G and H at each stage. -/
private def bf_chain
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (enumH : ℕ → H) : ℕ → BFIsoStep p (G := G) (H := H)
  | 0     => BFIsoStep.init p
  | n + 1 => (bf_forth_back p hforth hback
                (bf_chain hforth hback enumG enumH n) (enumG n) (enumH n)).choose

/-- Key monotonicity and coverage properties of consecutive chain steps. -/
private lemma bf_chain_step_props
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (enumH : ℕ → H) (n : ℕ) :
    let c := bf_chain p hforth hback enumG enumH
    ∃ (hle : (c n).A ≤ (c (n+1)).A),
      (c n).B ≤ (c (n+1)).B ∧ enumG n ∈ (c (n+1)).A ∧ enumH n ∈ (c (n+1)).B ∧
      ∀ a : (c n).A, ((c (n+1)).e ⟨a.val, hle a.prop⟩ : H) = (c n).e a :=
  (bf_forth_back p hforth hback
    (bf_chain p hforth hback enumG enumH n) (enumG n) (enumH n)).choose_spec

/-- The A-subgroups of the chain are monotone. -/
private lemma bf_chain_A_le
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (enumH : ℕ → H) {m n : ℕ} (hmn : m ≤ n) :
    (bf_chain p hforth hback enumG enumH m).A ≤
      (bf_chain p hforth hback enumG enumH n).A := by
  induction' n with n ih generalizing m
  · aesop
  · obtain rfl | hmn := hmn.eq_or_lt
    · rfl
    · obtain ⟨hle, _, _, _, _⟩ := bf_chain_step_props p hforth hback enumG enumH n
      exact le_trans (ih (Nat.le_of_lt_succ hmn)) hle

/-- The partial isomorphisms are compatible across chain stages. -/
private lemma bf_chain_compat
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (enumH : ℕ → H) {m n : ℕ} (hmn : m ≤ n)
    (a : (bf_chain p hforth hback enumG enumH m).A) :
    ((bf_chain p hforth hback enumG enumH n).e
      ⟨a.val, bf_chain_A_le p hforth hback enumG enumH hmn a.prop⟩ : H) =
    (bf_chain p hforth hback enumG enumH m).e a := by
  induction' hmn with n hmn ih
  · rfl
  · obtain ⟨hle, _, _, _, h⟩ := bf_chain_step_props p hforth hback enumG enumH n
    exact h ⟨a, bf_chain_A_le p hforth hback enumG enumH hmn a.2⟩ ▸ ih

/-- The B-subgroups of the chain are monotone. -/
private lemma bf_chain_B_le
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (enumH : ℕ → H) {m n : ℕ} (hmn : m ≤ n) :
    (bf_chain p hforth hback enumG enumH m).B ≤
      (bf_chain p hforth hback enumG enumH n).B := by
  induction' hmn with n hmn ih
  · rfl
  · exact le_trans ih (by have := bf_chain_step_props p hforth hback enumG enumH n; tauto)

/-- The limit map: send g to its image under the first chain stage that covers it. -/
private noncomputable def bf_limit_map
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H) (g : G) : H :=
  let n     := (hG_surj g).choose
  let c     := bf_chain p hforth hback enumG enumH
  let props := bf_chain_step_props p hforth hback enumG enumH n
  c (n + 1) |>.e ⟨g, by rw [← (hG_surj g).choose_spec]; exact props.choose_spec.2.1⟩

/-- The limit map evaluates consistently at any stage that already covers g. -/
private lemma bf_limit_map_eq_at
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H)
    (g : G) (n : ℕ) (hg : g ∈ (bf_chain p hforth hback enumG enumH n).A) :
    bf_limit_map p hforth hback enumG hG_surj enumH g =
      ((bf_chain p hforth hback enumG enumH n).e ⟨g, hg⟩ : H) := by
  by_cases h : n ≤ (hG_surj g).choose + 1
  · have := bf_chain_compat p hforth hback enumG enumH h ⟨g, hg⟩; aesop
  · convert bf_chain_compat p hforth hback enumG enumH
        (show (hG_surj g).choose + 1 ≤ n from by linarith) _ |>.symm using 1

/-- The limit map is additive. -/
private lemma bf_limit_map_add
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H)
    (g₁ g₂ : G) :
    bf_limit_map p hforth hback enumG hG_surj enumH (g₁ + g₂) =
    bf_limit_map p hforth hback enumG hG_surj enumH g₁ +
    bf_limit_map p hforth hback enumG hG_surj enumH g₂ := by
  obtain ⟨n₁, hn₁⟩ := hG_surj g₁
  obtain ⟨n₂, hn₂⟩ := hG_surj g₂
  set N := Nat.max (n₁ + 1) (n₂ + 1)
  have hg₁ : g₁ ∈ (bf_chain p hforth hback enumG enumH N).A := by
    have hg₁' : g₁ ∈ (bf_chain p hforth hback enumG enumH (n₁ + 1)).A := by
      have := bf_chain_step_props p hforth hback enumG enumH n₁; grind +ring
    exact bf_chain_A_le p hforth hback enumG enumH (Nat.le_max_left _ _) hg₁'
  have hg₂ : g₂ ∈ (bf_chain p hforth hback enumG enumH N).A := by
    have := bf_chain_step_props p hforth hback enumG enumH n₂
    simp [hn₂] at this
    exact bf_chain_A_le p hforth hback enumG enumH
      (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)))
      this.2.1
  have hg₁g₂ : g₁ + g₂ ∈ (bf_chain p hforth hback enumG enumH N).A :=
    AddSubgroup.add_mem _ hg₁ hg₂
  set eN := (bf_chain p hforth hback enumG enumH N).e
  rw [bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₁ N hg₁,
      bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₂ N hg₂,
      bf_limit_map_eq_at p hforth hback enumG hG_surj enumH (g₁ + g₂) N hg₁g₂]
  exact eN.map_add ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ ▸ rfl

/-- The limit map is injective. -/
private lemma bf_limit_map_injective
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H) :
    Function.Injective (bf_limit_map p hforth hback enumG hG_surj enumH) := by
  intro g₁ g₂ h_eq
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, g₁ ∈ (bf_chain p hforth hback enumG enumH (n₁ + 1)).A := by
    obtain ⟨n₁, hn₁⟩ := hG_surj g₁
    exact ⟨n₁, by have := bf_chain_step_props p hforth hback enumG enumH n₁; aesop⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n₂, g₂ ∈ (bf_chain p hforth hback enumG enumH (n₂ + 1)).A := by
    obtain ⟨n₂, rfl⟩ := hG_surj g₂
    exact ⟨n₂, (bf_chain_step_props p hforth hback enumG enumH n₂).choose_spec.2.1⟩
  set N := max n₁ n₂ + 1
  have hN₁ : g₁ ∈ (bf_chain p hforth hback enumG enumH N).A :=
    bf_chain_A_le p hforth hback enumG enumH (by omega) hn₁
  have hN₂ : g₂ ∈ (bf_chain p hforth hback enumG enumH N).A :=
    bf_chain_A_le p hforth hback enumG enumH (Nat.succ_le_succ (le_max_right _ _)) hn₂
  have h_eq_N :
      ((bf_chain p hforth hback enumG enumH N).e ⟨g₁, hN₁⟩ : H) =
      ((bf_chain p hforth hback enumG enumH N).e ⟨g₂, hN₂⟩ : H) := by
    rw [← bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₁ N hN₁,
        ← bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₂ N hN₂, h_eq]
  exact congrArg Subtype.val
    ((bf_chain p hforth hback enumG enumH N).e.injective (Subtype.ext h_eq_N))

/-- The limit map is surjective. -/
private lemma bf_limit_map_surjective
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG)
    (enumH : ℕ → H) (hH_surj : Function.Surjective enumH) :
    Function.Surjective (bf_limit_map p hforth hback enumG hG_surj enumH) := by
  intro h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, h ∈ (bf_chain p hforth hback enumG enumH n).B := by
    obtain ⟨n, rfl⟩ := hH_surj h
    exact ⟨n + 1, by
      simpa using (bf_chain_step_props p hforth hback enumG enumH n).choose_spec.2.2.1⟩
  let a := (bf_chain p hforth hback enumG enumH n).e.symm ⟨h, hn⟩
  use a.val
  have ha : (bf_chain p hforth hback enumG enumH n).e a = ⟨h, hn⟩ := by simp [a]
  rw [bf_limit_map_eq_at p hforth hback enumG hG_surj enumH a.val n a.prop]
  exact congrArg Subtype.val ha

/-- Back-and-forth assembly: abstract `hforth`/`hback` hypotheses for `BFIsoStep`
imply the two groups are isomorphic.  Proved in full; no `sorry` within.
Connecting this to `iso_of_ulmInvariant_eq` requires proving the hypotheses from
`socle_extend` — that step is deferred. -/
lemma iso_of_ulmInvariant_eq_of_backAndForth
    [Countable G] [Countable H]
    (hforth : ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a)
    (hback : ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
        ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
          h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a) :
    Nonempty (G ≃+ H) := by
  obtain ⟨enumG, hG_surj⟩ := exists_surjective_nat G
  obtain ⟨enumH, hH_surj⟩ := exists_surjective_nat H
  have h_bij : Function.Bijective (bf_limit_map p hforth hback enumG hG_surj enumH) :=
    ⟨bf_limit_map_injective p hforth hback enumG hG_surj enumH,
     bf_limit_map_surjective p hforth hback enumG hG_surj enumH hH_surj⟩
  exact ⟨{ Equiv.ofBijective _ h_bij with
             map_add' := fun x y => by
               simpa using bf_limit_map_add p hforth hback enumG hG_surj enumH x y }⟩

/-- Hard direction of Ulm's theorem: equal Ulm invariants imply isomorphism.
Pending: derive `hforth`/`hback` for `BFIsoStep` from the extension machinery
(requires `socle_extend`); then call `iso_of_ulmInvariant_eq_of_backAndForth`. -/
lemma iso_of_ulmInvariant_eq
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G)
    (hH : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal, ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) := by
  sorry

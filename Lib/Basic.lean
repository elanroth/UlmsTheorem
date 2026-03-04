import Mathlib

/-!
# Basic imports and shared notation — ACM project

This file is imported by all modules. It carries shared notation and
small utility lemmas that do not belong to a specific submodule.

## Project scope

We formalize:
1. **Ulm's theorem** (novel Lean formalization): two countable reduced
   abelian p-groups are isomorphic iff their Ulm invariants agree at every ordinal.
2. **Scott complexity** of countable reduced abelian p-groups, following
   Alvir–Csima–MacLean (ACM).  The main goal is a sharp classification of
   Σ/Π/d-Σ complexity of Scott sentences for groups of Ulm length ω·γ+n,
   including the rigid-tail case f(ω·γ) = … = f(ω·γ+n−2) = 0.
3. **Index-set complexity** comparison with Calvert's results.

## Notation

Throughout we work with additive abelian groups.
- `p ^ n • x` : the n-fold p-multiple of x (standard Mathlib nsmul)
- `pPow p n G` : Ulm subgroup p^n · G ⊆ G  (ℕ-indexed)
- `ulmSubgroup p α G` : Ulm subgroup p^α · G ⊆ G  (Ordinal-indexed)
- `ulmInvariant p α G` : dim_{ℤ/pℤ} (p^α G / p^(α+1) G)
- `ulmLength p G` : least α with p^α G = 0  (for reduced groups)
-/

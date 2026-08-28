# Ulm's theorem in Lean 4

A formalization of **Ulm's theorem**: two countable reduced abelian `p`-groups are
isomorphic if and only if they have the same Ulm invariants at every ordinal.

```
theorem ulm_theorem {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H) :
    Nonempty (G ≃+ H) ↔
      ∀ α : Ordinal.{0}, ulmInvariant p α (G := G) = ulmInvariant p α (G := H)
```

`Lib/Ulm/Theorem.lean`. Both directions are separate proved theorems
(`ulm_invariants_of_iso`, `iso_of_ulm_invariants`); the biconditional is their
conjunction.

## Statement fidelity

The classical statement, for comparison:

> **Theorem 14.** *Two reduced countable primary abelian groups are isomorphic if and
> only if they have the same Ulm invariants.*
> — Kaplansky, *Infinite Abelian Groups*, p. 27

with the invariant defined on the same page as the dimension of `P_α / P_{α+1}` over
`ℤ/p`, where `P = {x : px = 0}` and `P_α = P ∩ p^α G`. Fuchs states it as Theorem 1.6
(*Abelian Groups*, 2015, p. 346) with the UK-invariant on p. 344.

The Lean matches on every axis: it is a genuine biconditional, the conclusion is
`Nonempty (G ≃+ H)` rather than a one-sided embedding, the quantifier ranges over all
of `Ordinal.{0}` rather than `ℕ`, and countability and reducedness are both present and
both genuinely used. `ulmInvariant` is literally `Module.rank (ZMod p) (P_α ⧸ P_{α+1})`.

**Countability is load-bearing, not decorative.** Ulm's theorem is *false* without it —
Fuchs (Pergamon 1960) has a section titled "Non-isomorphic groups with the same Ulm
sequence" (§39, p. 134) giving a counterexample at cardinality `ℵ₁`, and Crawley,
*Pacific J. Math.* 22 (1967) 235–239 records the same failure. Removing `[Countable]`
and discharging the conclusion with `ulm_theorem` fails to synthesize the instance; the
proof consumes countability at `Lib/Ulm/Classification.lean` via `exists_surjective_nat`.

## Verifying it

Do not try to check completeness by grepping for `sorry` — that cannot see a hole in a
dependency, and neither can the editor's checkmarks. The real check is:

```bash
lake build Test.AxiomGate
```

`Test/AxiomGate.lean` pins the axiom lists of `ulm_theorem` and both directions with
`#guard_msgs`. If a `sorry`, a new axiom, or an unfinished dependency ever enters, the
build fails. The expected list is Lean's three standard axioms and nothing else.

## Non-vacuity

`Test/UlmDifferentialRegression.lean` derives a known non-isomorphism *from* the
theorem. `Z/4 ⊕ Z/4` and `Z/2 ⊕ Z/8` both have order 16, two cyclic summands, and socle
dimension 2 — only the Ulm invariant separates them. The file proves `f(0) = 0` for the
first and `f(0) ≠ 0` for the second, then concludes they are non-isomorphic. A
degenerate, mis-indexed, or group-blind invariant could not pass this.

For a finite direct sum of cyclics, `f(n)` counts the summands of order `p^(n+1)` — note
the off-by-one — so the two vectors are `0,2,0,…` and `1,0,1,…`. That formula is stated
in E. A. Walker, "Ulm's Theorem for Totally Projective Groups", *Proc. Amer. Math. Soc.*
37 (1973), 387–392, p. 387.

## Layout

| Path | Contents |
|---|---|
| `Lib/PGroups/` | `p`-groups, heights, the transfinite Ulm filtration `p^α G`, the socle, and the Ulm invariant |
| `Lib/Ulm/` | purity, Kaplansky's extension lemma, the back-and-forth assembly, and the theorem |
| `Test/` | the axiom gate, regression tests, and the differential test |

## Provenance

This repository was extracted from a larger private multi-project repository, retaining
the commit history of the files kept here. Nine of the twenty-four commit messages were
rewritten during extraction: their originals described work in a component that is not
part of this repository, and each rewritten message says so explicitly in a trailer and
describes only the changes to files retained here. No file contents were altered by the
extraction; the build configuration, this README, and `Test/AxiomGate.lean` are new.

The early history is candid about its tooling: several 2026-03 and 2026-04 commits are
bulk AI-assisted proving passes, and are named as such.

## License

Apache License 2.0 — see [LICENSE](LICENSE).

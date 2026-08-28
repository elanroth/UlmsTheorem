# Golf log

Passes over this repository under `maimonides/docs/lean-style.md`. Every row is a change kept only
because `lake build` was green, the axiom gate passed, and the statement-line diff was empty.

The "disagreements" column is the point of this file: it is the evidence that confirms or kills a
rule in the style document.

---

## Pass 1 — 2026-08-28 — the linter's own findings

**Scope.** Every warning the green build already prints. No proof was read for mathematics; this is
tier A of the catalog plus two tier-B line merges.

| Metric | Before | After |
|---|---|---|
| Linter warnings | 16 | 2 |
| Lines (`Lib/**`) | 3646 | 3641 |
| Public declarations | unchanged | unchanged |
| Statement-line diff | — | empty |
| `lake build` | green, 8305 jobs | green, 8305 jobs |

Per file: `Extension.lean` 1730 → 1718, `UlmSubgroups.lean` 139 → 138, `Heights.lean` 166 → 166,
`Classification.lean` 329 → **337**.

**What changed.**

- 8 × `simpa … using e` → `simp …` where `linter.unnecessarySimpa` said the `using` term was dead.
  Three of these carried a 3–6 line term that was doing nothing; deleting them is where nearly all
  the line saving came from.
- 4 × unused `simp` arguments dropped (`QuotientAddGroup.lift_mk`, `Int.mul_left_comm`,
  `Int.mul_assoc` ×2), per `linter.unusedSimpArgs`.
- 2 × `convert … using 1 <;> abel` → two lines, per `linter.unnecessarySeqFocus`: there was one
  goal, so `<;>` advertised branching that does not exist.
- 1 × `push_neg` → `push Not` (deprecation).
- 7 × `omit hp in` on private lemmas in `Classification.lean` that never use `[Fact p.Prime]`.
- 2 `rw` calls merged into one in `UlmSubgroups.lean`.

**Disagreements between the metric and readability.**

1. **`Classification.lean` got 8 lines longer and is better for it.** Seven `omit hp in` lines are
   pure addition, and they buy a true statement: those lemmas are back-and-forth bookkeeping and
   genuinely do not need `p` prime. Line count is the wrong scorer here, exactly as
   `lean-style.md` §3 anticipated. Kept.
2. **The `simp` args are only *reported* unused, not *proved* unused.** `linter.unusedSimpArgs`
   observes the current proof term. Kept because the kernel re-checked, but this is a rule that
   should stay tier A only while the build is the gate.

**Two things deliberately NOT done.**

- **`iso_of_ulmInvariant_eq_of_backAndForth` still warns `unusedSectionVars`.** It is *public*, so
  `omit hp in` would delete `[Fact p.Prime]` from its signature — a statement change, forbidden by
  §2 rule 4, and it breaks call sites. It is also mathematically interesting: the warning is
  evidence the theorem may not need primality at all. **This is a question for Elan, not a golf
  move.**
- **`Ordinal.add_succ` deprecation in `UlmSubgroups.lean:104` is a bad upstream deprecation.**
  Mathlib redirects it to `add_assoc`, which is a different statement (`a + succ b = succ (a + b)`
  versus `a + b + c = a + (b + c)`) — the warning even prints the differing type. Tried
  `rw [natCast_succ, ← add_assoc, …]`; it failed with "did not find an occurrence of the pattern",
  and was reverted. **The warning stays until mathlib fixes the alias.** New rule for the style
  doc: a deprecation warning is tier A *only* when the replacement has the same type; when the
  warning itself prints "the updated constant has a different type", it is tier C.

**Cascade note.** Fixing warnings surfaced new ones three times — `simpa → simp` exposed four newly
unused `simp` args, and each `omit hp in` exposed the next lemma in the chain. A warning pass is a
loop until dry, not a single sweep. That belongs in the tooling section of the style doc.

---

## Pass 2 — 2026-08-28 — `exists_kaplanskyTarget_caseI`, end to end

**Scope.** One declaration, the longest in the repository, golfed with the mathematics read first.
Tiers A, B and C. Calibration case for whether the style document's ranked objective produces the
right result on a real proof.

| Metric | Before | After |
|---|---|---|
| Proof body lines | 114 | 60 |
| Statement | — | **byte-identical** (checked by extraction, not by eye) |
| `Lib.Ulm.Extension` build | 11s | 11s |
| Linter warnings | 2 | 2 (no new) |
| `lake build` | green, 8305 jobs | green, 8305 jobs |

**The argument, so the next reader has it.** `x` has exact height `α`, is proper over the stage
`s.A`, and among proper translates maximizes `h(p • y)`; Case I is `p • x ∉ G_{α+2}`. Since
`x ∈ G_α`, `p • x ∈ G_{α+1}`, so its image has a root `w ∈ H_α`; Case I forces `w ∉ H_{α+1}`, giving
three of the four conjuncts. Properness of `w` is the content: a translate `w + t` of height `> α`
pulls back along `e⁻¹` to `a ∈ s.A`, and `y = x + a` is then a proper translate of `x` with
`h(p • y) ≥ α+2`, contradicting maximality (`h(p • x) ≤ α+1` by Case I).

**Where the 54 lines went.**

- **A `let z := s.e ⟨p • x, hpxA⟩` that cost more than it saved: 14 lines.** Naming the image forced
  three `change` blocks later to unfold it again, because `hpw` and the goal are both stated in the
  unfolded form. Inlining `z` deleted all three. **New rule, promoted to the style doc:** a `change`
  block in generated Lean is nearly always the receipt for a badly-chosen `let` — look up, not at
  the `change`.
- **`ulmHeight_eq_of_mem_not_mem_succ p x α hxα hxSucc` was computed twice**, in two different
  `have`s 13 lines apart. Hoisted to `hxHeight` at the top, used three times.
- **9 × `intro h; exact f h` → `fun h ↦ f h`,** and `apply X; exact/simpa …` → `X (by simpa …)`.
  This is the single most frequent residue in the file.
- **Two `absurd` chains replaced ~20 lines of `have hlower/hupper1/hupper2/hbad` bookkeeping.** The
  named intermediates were not steps of the mathematics, they were the prover writing down its
  transitivity chain. `(a.trans (b.trans c))` says the same thing and reads as the inequality it is.

**Disagreements between the metric and readability — and what I did NOT compress.**

1. **I added four comments (net +4 lines) naming the phases of the argument.** Nothing in the
   original said *why* `y = x + a` is formed. Per §1 goal 2, that is the file getting better while
   the metric gets worse. Kept.
2. **`hyProper`, `hycoset`, `hpyA`, `hepy` keep their names even though each is used once.** These
   are the four facts the maximality hypothesis consumes; they are the mathematics, and §1 goal 3
   says a load-bearing step keeps its line. Inlining them would have bought maybe 6 more lines and
   made the final `absurd` unreadable.
3. **`push_cast` beat `change`.** The `rw` chain in `hepy` ends with the subgroup coercion sitting
   outside a sum, so `← hpw` cannot match. The original solved this with two `change` blocks; one
   `push_cast` does it. **New tier-B entry:** when a `rw` chain fails on a coercion boundary, reach
   for `push_cast` before restating the goal by hand.

**Nothing about the proof's mathematics changed.** No `exact?` search found a mathlib replacement
for any step here — this proof is about the local stage interface (`hφ_at` / `hφ_succ` /
`hφ_succSucc`), which has no mathlib analogue. Tier C on this declaration was structural, not
lemma-substitution.

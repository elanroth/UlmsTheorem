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

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

---

## Pass 3 — 2026-08-28 — `exists_kaplanskyTarget_caseII`, and the lemma it exposed

**Scope.** The sibling case, golfed the same way. It turned out to share an argument with Case I —
and with two further sites elsewhere in the file — so this pass is the first tier-C
*lemma-extraction*, not just restructuring.

| Metric | Before | After |
|---|---|---|
| `exists_kaplanskyTarget_caseII` proof lines | 103 | 41 |
| `exists_kaplanskyTarget_caseI` proof lines | 60 | 54 |
| `Lib/Ulm/Extension.lean` | 1664 | 1577 |
| Declarations | — | **+1** (`isProper_iff_forall_not_mem_succ`, in `Pure.lean`) |
| Statements | — | **all byte-identical**; the statement-line diff shows exactly one `+`, the new helper |
| `Lib.Ulm.Extension` build | 11s | 11s |
| Linter warnings | 2 | 2 |
| `lake build` | green, 8305 jobs | green, 8305 jobs |

**The finding: one lemma was written out longhand four times.**

Every occurrence had the shape *"`u` has exact height `α` and is proper over `S`; suppose a
translate `u + c` reaches `G_{α+1}`; then `α+1 ≤ h(u+c) ≤ h(u) = α`, contradiction"* — spelled out
each time as `have hlower / hupper / hheight / hbad`, then
`not_le_of_gt (WithTop.coe_lt_coe.mpr (Order.lt_succ α)) hbad`. About 12 lines per copy.

Both directions were in use, so it is an iff, now in `Lib/Ulm/Pure.lean` next to `IsProper`:

```lean
lemma isProper_iff_forall_not_mem_succ [Fact p.Prime] (S : AddSubgroup G) {x : G}
    {α : Ordinal.{0}} (hx : x ∈ ulmSubgroup p α (G := G))
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    IsProper p S x ↔ ∀ c : S, x + (c : G) ∉ ulmSubgroup p (Order.succ α) (G := G)
```

It replaced four hand-written copies (Case I ×1, Case II ×2, `Extension.lean:1044` ×1) plus a fifth
variant at `Extension.lean:383` that needed only a negated element. **19 lines added, 127 removed.**

That is also the right *mathematical* statement of what properness means at a known exact height,
which is why it belongs beside `IsProper` rather than inside either case — §1 goal 2 and goal 4
agreeing for once.

**On whether the framework scales — the actual question this pass was run to answer.**

It scaled better than Pass 2, in a specific way: **Case II needed almost no fresh judgment.** The
Pass 2 rules (`change` is a bad `let`'s receipt; hoist the twice-computed `have`; `intro h; exact`
→ term; a chain of named inequalities is transitivity written out) applied directly, and Case II's
proof body fell 60% against Case I's 47%. Both the helper and the rewritten Case II compiled on the
**first** attempt, where Pass 2 needed one `push_cast` repair.

The part that did *not* transfer mechanically is the part worth keeping a human on: noticing that
four scattered blocks were the same lemma. No linter suggests that, `exact?` cannot find a lemma
that does not exist yet, and it was only visible after reading two proofs in full. **The tiers hold
up: A and B are automatable, C is where a person or a careful agent earns its keep.**

**Disagreement between the metric and readability.** One, and it went the metric's way this time:
`Case I` lost `hwHeight` and `hySucc`'s six-line body, both of which I had *kept* in Pass 2 on
goal-3 grounds. Once the helper existed they stopped being load-bearing steps and became
restatements of it. **Rule learned: goal 3 ("load-bearing steps stay visible") is relative to the
available vocabulary. Extracting a lemma can demote a step that was previously worth naming — so
re-read earlier golfed proofs after adding a helper.**

---

## Pass 4 — 2026-08-28 — the three next-longest declarations, in one pass

**Scope.** `socle_extend_build_map`, `proper_adjoin_rep_mem_iff`, `kaplansky_extend_one_of_target`
together. Run as one pass to test whether the rules now apply without per-declaration deliberation.

| Metric | Before | After |
|---|---|---|
| `socle_extend_build_map` proof lines | 93 | 44 |
| `proper_adjoin_rep_mem_iff` proof lines | 68 | 30 |
| `kaplansky_extend_one_of_target` proof lines | 60 | 30 |
| `Lib/Ulm/Extension.lean` | 1577 | 1460 |
| Declarations in `Extension.lean` | 53 | 53 (none added, none removed) |
| Statements | — | **all 53 byte-identical**, checked by extraction |
| `Lib.Ulm.Extension` build | 11s | 10s |
| Linter warnings | 2 | 2 |
| `lake build` | green, 8305 jobs | green, 8305 jobs |

**The find: a lemma re-proved 60 lines above its own statement.** `socle_extend_build_map` proved
`(p : ℤ) ∣ z.2` inline with a 24-line Bézout argument (`Nat.Coprime`, `Int.gcd_eq_gcd_ab`, an
explicit `calc` for `g = gcdA • (n • g) + gcdB • (p • g)`). `dvd_of_zsmul_mem_of_not_mem`, four
declarations further down **in the same file**, is exactly that statement, proved in eight lines via
`addOrderOf` in the quotient. Moving the existing lemma above its duplicate and calling it: **24
lines → 2.**

This is worse than the Pass 3 case and more instructive. In Pass 3 the shared lemma did not exist
and had to be invented. Here it existed, was already correct, already used by a neighbouring
declaration, and was *still* re-derived by hand — because the two were written in different sessions
and nothing links them. **A duplicate-detection sweep is worth running over any AI-written Lean
file before golfing it**: grep the statements, not the proofs.

**Second helper extracted**, into `Lib/PGroups/UlmSubgroups.lean` beside the filtration it is about:

```lean
lemma add_zsmul_mem_iff_of_mem {β : Ordinal.{0}} {x c : G}
    (hx : x ∈ ulmSubgroup p β (G := G)) (n : ℤ) :
    c + n • x ∈ ulmSubgroup p β (G := G) ↔ c ∈ ulmSubgroup p β (G := G)
```

`proper_adjoin_rep_mem_iff` contained this argument twice — once for `G` and once verbatim for `H`,
24 lines total — because the lemma is a source/target comparison and the prover wrote each side out.
**Symmetric duplication across the two groups is a shape to look for in this repo specifically.**

**Other findings.**

- **`hraw_inj` in `kaplansky_extend_one_of_target` was dead** — five lines defining an injectivity
  fact nothing referenced (`grep -c` returns 1, its own definition). Deleted.
- **Eight `change` blocks in `kaplansky_extend_one_of_target`**, including `change b ∈ B'` followed
  immediately by `change b ∈ AddMonoidHom.range raw` — a `let` unfolded in two steps. The Pass 2
  rule fired unmodified: most disappeared by inlining the `let`s into the structure literal that
  consumed them, and the final `∀ a, …` obligation closed as `fun a ↦ hfA a` with no `change` at all.
- **`push_cast` must come *before* the rewrite it enables, not after.** Pass 2 established
  `push_cast` over `change` at a coercion boundary; this pass got the ordering wrong first
  (`rw [map_add, map_zsmul, ← hpw]; push_cast`) and the `← hpw` failed to match. Correct order is
  `rw [map_add, map_zsmul]; push_cast; rw [← hpw]`. **This was the pass's only build failure.**

**Did the rules apply without fresh deliberation?** Largely yes. Three declarations, ~180 proof
lines removed, and exactly one compile error across the whole pass — the `push_cast` ordering, which
was a refinement of an existing rule rather than a new problem. The two things that still needed a
person were both *recognition* problems, not rewriting problems: seeing that an existing lemma was
being re-proved, and seeing that two 12-line blocks were the same argument on `G` and on `H`.

**Logged, not done: `fun x => ` vs `fun x ↦`.** The repo is 44 `=>` to 12 `↦`; mathlib style (and
§4) is `↦`. New code in this pass uses `↦`, so the file is now mixed. This is a safe mechanical
sweep but it would swamp a golf diff, so it is left as its own one-line change for Elan to approve
rather than smuggled in here.

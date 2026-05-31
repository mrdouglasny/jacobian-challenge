# Validation plan — judging the definitions and axioms before proving them

_Authored 2026-05-31. Companion to [`status-2026-05-31.md`](status-2026-05-31.md)
and [`dependency-trace.md`](dependency-trace.md)._

This repo closes Buzzard's 24 sorries by reducing them to **definitions +
named axioms**, verified at the kernel level (`#print axioms` shows core-3
axioms + named project axioms, **no `sorryAx`**, on all 24 declarations and
the `genus` headlines). That makes the natural next question not "are the
proofs done" but **"are the definitions and axioms the right ones?"** —
because a wrong axiom blocks a later proof, but a wrong *definition* makes
every downstream theorem vacuous or meaningless, and an axiom that *asserts*
a definition behaves well can silently paper over a bad definition.

This document is the plan for answering that, in three layers:

1. **Mechanical checks** — cheap, kernel-backed, scriptable into CI.
2. **The validation backlog** — concrete, prioritized experiments that
   convert "asserted" into "proven on a witness".
3. **Improving validation** — a human-readable contract format and an
   AI-modelable specification-first pipeline, so that judging the repo
   does not require reading Lean proofs.

---

## Part 0 — The core asymmetry

Split everything the repo asserts into two kinds, because they fail
differently and need different validation:

| | Failure mode | What catches it |
|---|---|---|
| **Definitions** (`genus`, `Jacobian`, `ofCurve`, `HyperellipticEvenProj`, …) | *vacuous* (returns 0 / ⊥ / trivial), or *wrong object* (type-checks but isn't the textbook object) | concrete-witness theorems proven **without** project axioms |
| **Axioms** | *unsound* (too strong / contradictory → `False`), *vacuous* (hypotheses unsatisfiable → asserts nothing), or *misquoted* (doesn't match the textbook) | non-vacuity instantiation, consistency smell-test, human review against the source |

The dangerous overlap is the **definition-asserting axiom**: an axiom of
the form "the construction I just defined has the good property P".
`AX_ofCurve_inj` (Abel–Jacobi is injective — Buzzard's anti-`J(X)=0` hack)
and `AX_genus_eq_zero_iff_homeo` are exactly this. They are currently
*asserted*. Until one of them is discharged on a concrete curve from the
real definition, we have not validated that `ofCurve` / `genus` are not the
degenerate hack the challenge is designed to forbid. **This is the
single highest-value validation target in the repo.**

---

## Part 1 — Mechanical checks (do first; lock into CI)

### 1.1 Axiom-trace golden file (`#print axioms`)

`#print axioms D` prints the *complete transitive* axiom dependency of `D`
and surfaces any `sorryAx`. Run it on every tracked headline; commit the
output as a golden file; CI fails if the set changes (new axiom creeps in,
or a `sorryAx` appears). Starter at [`scripts/axiom_report.lean`](../scripts/axiom_report.lean):

```bash
lake env lean scripts/axiom_report.lean > docs/axiom-report.txt
git diff --exit-code docs/axiom-report.txt   # CI guard
```

This permanently locks in "no hidden sorry under any headline" and makes
every axiom-set change a reviewed diff. It is the cheapest guarantee we
can buy and it never goes stale.

### 1.2 Non-vacuity sentinels (per existence/structure axiom)

An existence axiom `∃ f, spec f` is worthless if `spec` is unsatisfiable,
and *dangerous* if `spec` is self-contradictory (it then inhabits an empty
type and yields `False`). A `∀`-axiom with unsatisfiable hypotheses asserts
nothing. For each such axiom write a **sentinel obligation**: instantiate
the hypotheses (or the existential's spec) on a concrete witness and check
it is satisfiable / non-trivial. The repo has already been bitten twice —
`AX_FiniteDimOneForms`-as-instance over a `True∧True` carrier produced
`False`, and the EvenForm Möbius axioms were unsound until tightened
(2026-04-26). Those are the template; every existence axiom should carry
its own sentinel.

### 1.3 Consistency smell-test (per high-leverage axiom)

Mathlib has no inconsistency detector. But for each load-bearing axiom,
spend a few minutes on `example : False := by <try to exploit it>`. This
proves nothing positive but reliably catches the cheap exploits (rank
collapse, vacuous existentials, quantifier inversion). Record the negative
result next to the axiom.

---

## Part 2 — Axiom taxonomy by validation risk

The ~100 axioms split into four buckets that each need a *different* kind
of validation. (Names below are representative, not exhaustive; the full
tagging is in [`dependency-trace.md`](dependency-trace.md).)

### A. Classical-theorem axioms — *validate by faithful-encoding review*
`AX_RiemannRoch`, `AX_SerreDuality`, `AX_RiemannBilinear`, `AX_AbelTheorem`,
`AX_BranchLocus`, `AX_PluckerFormula`, `AX_genus_eq_zero_iff_homeo`
(uniformization, genus 0), `AX_AnalyticCycleBasis`,
`AX_Liouville_compact_complex_manifold`.

Sound by citation — *if* the Lean statement faithfully encodes the
textbook theorem. The only real risk is mis-encoding: hypotheses too weak
(→ unsound), too strong (→ undischargeable), or a wrong conclusion. **The
validation is a human mathematician diffing the Lean statement against the
named source.** LLM cross-vetting (Gemini's 6-criteria pass) is a filter,
not a substitute; none has had human review yet.

### B. Data-existence axioms — *validate by non-vacuity + discharge plan*
`pathIntegralBasepointFunctional`, `loopIntegralToH1`, `pullbackOneForm`,
`pushforwardOneForm`, `localOrder`, the `bridgePath*` family, `intersectionForm`,
`periodMap`, `AX_PeriodLattice` / `instPeriodLatticeDiscrete`,
`Divisor`/`LineBundle`/`H0`/`H1`/`canonicalDivisor`, `abelJacobiDiv`,
`infinityChart`/`infinityInverseMap`.

Each asserts an object/function exists with a spec. Risk: contradictory
spec (→ `False`) or vacuous spec (asserts nothing). Validation = the
non-vacuity sentinel (Part 1.2) + a written construction plan naming the
Mathlib pieces it would consume (already done for 5 of these in
[`construction-plans/`](construction-plans/)).

### C. Definition-asserting axioms — *validate by concrete-witness discharge* ⚠️
`AX_ofCurve_inj`, `AX_genus_eq_zero_iff_homeo`, `AX_ofCurve_contMDiff`,
`AX_pushforward_contMDiff` / `AX_pullback_contMDiff`,
`AX_pushforward/pullback_id_apply` / `_comp_apply`,
`AX_pushforwardAmbient_preserves_lattice` / `AX_pullbackAmbient_preserves_lattice`,
`AX_pushforward_pullback`, `AX_IntersectionForm_alternating` / `_perfect`.

These assert that a *construction we defined* behaves correctly. They are
the disguised risk: each could be masking a degenerate definition.
Validation = **discharge the property on a concrete instance from the real
definition** (e.g. prove `ofCurve` injective on `Elliptic` without
`AX_ofCurve_inj`). This validates the definition and the axiom at once.

### D. Atlas / structure axioms — *validate by chart-data sanity + eventual atlas proof*
`Hyperelliptic.*` (type + 7 instances + genus), `PlaneCurve.*` (type + 7
instances), `OddAtlas/InfinityChart.*`, `EvenAtlas` compat,
`hyperellipticEvenCoeff_cocycle_*_axiom`, `AffineForm` IFT-shape axioms,
`AX_HyperellipticAffine_connected`, `AX_PlaneCurveAffine_*`,
`contDiffOn_symm_toOpenPartialHomeomorph`.

Classical atlas constructions for specific curves; discharge is real chart
work. Until then, validate the *chart data* numerically/symbolically (the
transition maps compose correctly on sample points) and keep the
unified-type instances pinned by `≃ₜ` to the real parity cases (already
done) so they can't drift from the validated constructions.

---

## Part 3 — The validation backlog (prioritized)

1. **CI axiom-trace guard** (Part 1.1) — ~1 hr, permanent.
2. ~~**Discharge the genus-side anti-hack on a witness**~~ — **DONE
   (2026-05-31).** `genus ProjectiveLine = 0` is now proved *directly*: a
   chart-cocycle + Liouville argument shows `HolomorphicOneForm ℙ¹` is a
   subsingleton (`Line/OneForm.lean`, ~250 LOC, axiom-free), and `finrank`
   of a subsingleton is 0. `AX_genus_eq_zero_iff_homeo` is retired from the
   ℙ¹ genus cell (`proven_via_axiom → PROVEN_CORE_AXIOMS`); `genus ℙ¹` and
   `genus Elliptic` are now both core-axioms-only. The dependency was
   inverted: `OneForm` proves the subsingleton from first principles and
   `Genus` derives the value from it. (The `ofCurve_inj` analogue is **not**
   here — see the note below; it is blocked upstream.)
3. **Make `pathIntegralBasepointFunctional` concrete on `Elliptic`** — the
   real prerequisite for validating `ofCurve` at all. Wire in
   `kirovBackedFunctional` (needs the FTC theorem
   `kirovBackedFunctional_local_antiderivative`, currently `sorry`) or a
   bespoke genus-1 integral. **Only after this** can `ofCurve_inj` be
   discharged on a witness (see [`contracts/ofCurve.md`](contracts/ofCurve.md)).
4. **Non-vacuity sentinels** for all bucket-B axioms, starting with the
   five data-level ones on the critical path.
5. **Human review** of the ~10 bucket-A classical statements against their
   textbook sources (Forster, Miranda, Griffiths–Harris, Mumford *Tata I*).
6. **Grow the known-value table** — every new genus/period value proven on
   a concrete family is an independent definition check. You already have
   genus 0, 1, and even-hyperelliptic `N/2−1`; odd-hyperelliptic adds one.

> **Finding (2026-05-31).** Attempting to discharge `ofCurve_inj` on
> `Elliptic` revealed it is **opaque-blocked**: `ofCurve` bottoms out in the
> axiom `pathIntegralBasepointFunctional`, which has no concrete value on any
> curve, so injectivity is unprovable from the definition (it is consistent
> with the zero functional). This is the sharpest instance of the bucket-C
> risk and reorders the backlog — concrete validation of `ofCurve` is
> downstream of item 3, not a cheap early win. Full record:
> [`contracts/ofCurve.md`](contracts/ofCurve.md).

`genus_Elliptic_eq_one` already discharges from **core axioms only** — it
is the existence proof that the whole period-lattice/1-form machinery
computes the correct nonzero genus on a known curve. Every item above is,
in effect, "make another cell of the validation matrix look like that one."

---

## Part 4 — Improving validation: contracts + a specification-first pipeline

The goal: let a human (or a reviewing AI) **judge the repo without reading
the Lean proofs**, and let an AI **model the validation process** the way a
mathematician reads a new construction from a textbook — by checking it
against informal expectations before trusting any proof.

### 4.1 Object contracts (human-facing surface)

For each *constructed object* — not each theorem — maintain a one-screen
card. The reader judges the card; the Lean is the appendix.

```yaml
object: genus
informal: >
  The genus of a compact Riemann surface X: the complex dimension of the
  space of holomorphic 1-forms, equivalently the number of handles.
sources: [Forster §17, Miranda Ch. VI]
lean: "Jacobians.RiemannSurface.genus : (X : Type*) → … → ℕ"
characterization:          # the informal "what must be true", as claims
  - "genus(sphere) = 0"
  - "genus(torus / elliptic curve) = 1"
  - "genus(hyperelliptic y²=f(x), deg f = N) = ⌈N/2⌉ − 1"
  - "genus ≥ 0, and = 0 iff X ≃ sphere"     # anti-degeneracy
known_values:              # the test matrix — expected vs current status
  - {instance: ProjectiveLine,     expected: 0, status: proven_core_axioms}
  - {instance: Elliptic,           expected: 1, status: proven_core_axioms}
  - {instance: HyperellipticEven,  expected: "N/2−1", status: proven_mod_liouville}
  - {instance: HyperellipticOdd,   expected: "(N−1)/2", status: sorry}
anti_degeneracy:           # what would prove the definition is the hack
  - "must not be ≡ 0 on positive-genus curves (was a real bug via ⊥ submodule)"
axiom_deps: [from #print axioms — auto-filled]
status: validated_on {ProjectiveLine, Elliptic}; asserted elsewhere
```

A reviewer reads `informal` + `known_values` + `status` and immediately
sees *what the object is meant to be* and *where it is actually proven vs
asserted* — no proof reading. The `known_values` table is the
machine-checkable heart: each row is "object, instance, expected value,
proof status", i.e. **differential testing for mathematics**.

Write cards for the ~8 core objects first: `genus`, `Jacobian`, `ofCurve`,
`pushforward`/`pullback`, `HyperellipticEvenProj`, `Elliptic`, the period
lattice.

### 4.2 Specification-first formalization (the AI-modelable process)

The expensive step is *proving*; the high-value step is *formalizing the
specification*, and they should be separated. The pipeline mirrors how a
mathematician validates a new definition from a textbook:

```
 ① INFORMAL HARVEST   From the source, extract structured natural-language
                      claims about the object: its definition, its defining
                      properties, worked examples, known values, edge cases.
                      Each claim carries a citation. (Cheap, LLM-native.)

 ② SPEC FORMALIZE     Translate each claim into a Lean *statement* — a
                      `theorem … := by sorry` or a `Prop` — NOT a proof.
                      This is the characterization spec. Reviewable in
                      minutes; catches definition errors before any proof
                      effort. The sorry here is honest: it marks
                      "specified, not yet proven", and feeds the object card.

 ③ WITNESS / VACUITY  Auto-generate obligations: instantiate the spec on
                      each known example, assert the known value, assert the
                      anti-degeneracy property. These become the test
                      theorems and non-vacuity sentinels.

 ④ TRIANGULATE        A second model family re-derives the spec from the
                      same source and DIFFS against ②. Disagreement on the
                      informal claim or its Lean encoding = flag for human.
                      (This is where today's ad-hoc Gemini/Codex vetting
                      becomes a repeatable gate.)

 ⑤ PREPARE-TO-PROVE   Emit a discharge plan per spec: which Mathlib lemmas,
                      which prior axioms, estimated effort. An axiom is
                      "honest debt" exactly when it has a ⑤ attached.

 ⑥ PROVE              Only now attempt proofs, easiest-first: concrete
                      instances (③) before the general theorem, because a
                      proven instance validates the definition and a general
                      proof does not, if the definition is wrong.
```

Most validation value lives in ①–④, which today happen informally and
unrecorded. Making them explicit artifacts (the object cards + the
spec-`sorry` theorems + the triangulation diffs) is what lets a human
judge, and lets an AI *re-run the judgement* deterministically.

### 4.3 What an AI validation harness does each pass

Given the cards + the axiom report, a validation agent can run
autonomously and produce a reviewable report:

- **Refresh the axiom report** and diff against the golden file; flag any
  new axiom or `sorryAx`.
- **Recompute the known-value matrix** status (proven-core / proven-mod-axioms
  / sorry) by `#print axioms` on each cell's theorem; flag drift.
- **Check every existence axiom has a live non-vacuity sentinel**; flag the
  ones that don't.
- **Diff each object card's `informal`/`characterization` against the cited
  source** (triangulation, step ④) and flag mismatches for human sign-off.
- **Propose the next-cheapest validation** — usually "discharge property P
  on the smallest concrete instance", e.g. the anti-hack lemma on `Elliptic`.

The human reviews a short report of *flags and proposals*, not the codebase.
The invariant the harness enforces: every load-bearing claim is in exactly
one state — **proven-from-Mathlib**, **proven-on-a-witness + axiom for the
general case**, or **asserted with a discharge plan** — and nothing is
silently in a fourth state ("asserted, looks fine, never checked").

---

## Summary

- **Now:** kernel-verified that nothing hides a sorry (Part 1.1) and that
  `genus_Elliptic_eq_one` needs no project axioms — that is the model of a
  validated definition.
- **Cheapest next win:** CI axiom-trace guard + discharge one anti-hack
  lemma on a concrete curve (Parts 1.1, 3.2).
- **The structural fix:** object contracts + a specification-first pipeline
  that separates *formalizing the spec* (cheap, human-reviewable, catches
  definition bugs) from *proving it* (expensive), and lets an AI re-run the
  judgement as a deterministic report rather than a one-off vetting pass.

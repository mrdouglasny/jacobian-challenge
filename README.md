# Jacobians of Compact Riemann Surfaces

*Blow-by-blow discharge history lives in [`docs/history.md`](docs/history.md);
this file keeps the current state and the ideas.*

A Lean 4 formalization of [Kevin Buzzard's **Jacobian Challenge**](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9)
(spec v0.4, May 2026). Three headline results:

- **The challenge is closed.** All 24 `sorry`s in `Challenge.lean` are filled
  with real `def`s and `instance`s, and the anti-degeneracy theorems Buzzard
  built it around (correct genus, injective Abel–Jacobi) are proved — together
  with the Albanese **universal property** and **Riemann–Roch / Serre duality**.
- **The 24 are axiom-free.** Every Buzzard headline now `#print axioms`-checks to
  the three standard Lean axioms — `AX_PeriodCycleBasis`, the last
  challenge-critical axiom, was discharged from every headline closure by reproving
  the period lattice from a now-unconditional topology theorem (T-GEN) plus a ℙ¹
  unification (PRs #248/#250/#251). It survives only as *declared*, non-headline
  scaffolding for Riemann's bilinear relations.
- **The 24 do not pin the Jacobian** — as Buzzard himself anticipated in the
  challenge thread — we make the gap precise with a machine-checked counterexample
  and formalize the universal property (proposed there by Stoll and Merten) as the
  repair.

> **What this is, honestly.** A scaffold that *closes Buzzard's interface* and
> proves real theorems on it. The 24 headlines are now **axiom-free** (depend only
> on the three core Lean axioms), but they rest on a large vendored analytical
> engine (the Kirov Dolbeault port) and the surrounding Lean is AI-authored and
> **has not had independent human-mathematician review** — read this as a
> machine-checked *reduction*, **not** a from-first-principles textbook proof of
> Jacobian theory. See [Caveats](#caveats) before relying on any result.

## At a glance

| | |
|---|---|
| **Buzzard API** | 24/24 `sorry`s closed as real `def`s / `instance`s; machine-checked against the pinned v0.4 spec |
| **Challenge-critical axioms** | **0** — all 24 headlines are `#print axioms` standard-3 (`AX_PeriodCycleBasis` discharged from every headline closure, PRs #248/#250/#251; machine-checked: 0 mentions in [`docs/axiom-report.txt`](docs/axiom-report.txt)) |
| **Axioms** | 7 active, **none on the Buzzard headline path** — the **Albanese universal-property characterization is now axiom-free**: AK `AX_curve_image_subgroup_isOpen` was **discharged 2026-06-16 (PR #255, @daouid)**, so `ofCurve_isJacobian` `#print axioms` = std-3 (and `isJacobian_unique` was already axiom-free); A1 `AX_torus_uniformization` remains declared but out of every headline closure. The rest: intersection-form laws, Plücker, concrete-curve witnesses, and `AX_PeriodCycleBasis` (kept only as non-headline R1/R2 bilinear-relations scaffolding) — live count in [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) |
| **Beyond the challenge** | Riemann–Roch + Serre duality proved as theorems; Albanese categoricity proved; explicit positive-genus curve instances |
| **`sorry`s** | 0 in the core / challenge path; a handful in out-of-scope extensions and an optional adelic `H¹` construction |
| **Build** | `lake build` green; Lean `v4.30.0`, Mathlib pinned in `lake-manifest.json` |
| **Provenance** | our own Lean (~50k LOC) + the Kirov Dolbeault port (~86k LOC, a forward-port vendored in-tree under `vendor/` and built as a local Lake package) + vendored Kirov/Wallace modules (Apache 2.0 / MIT) |

Every headline is `#print axioms`-checked (golden trace in
[`docs/axiom-report.txt`](docs/axiom-report.txt), CI-diffed): it depends only on
the axioms it names plus the three Lean-core axioms, never `sorryAx`.

## The challenge

Buzzard's `Challenge.lean` defines an API for the Jacobian of a compact Riemann
surface, the Abel–Jacobi map, and pushforward/pullback functoriality — with 24
`sorry`s to fill (6 definitions, 7 typeclass instances, 11 theorems). The design
is **adversarial**: the API cannot be satisfied by a hack such as `Jacobian := 0`,
because `genus_eq_zero_iff_homeo` forces `genus` to be correct at 0 and
`ofCurve_inj` forces the Abel–Jacobi map to be genuinely injective in positive
genus. The underlying mathematics is classical (Abel 1829, Jacobi 1851); the task
is to formalize it on current Mathlib.

The deeper point is **validation, not just compilation**: the Lean kernel checks
*proofs*, never that a `def` *means* what it should, so a degenerate definition
can still compile. Buzzard defends against this by attaching independent
obligations to each definition. This repo pushes the same idea further — see the
next section.

## Do the 24 requirements pin the Jacobian?

**Not on their own — a subtlety the challenge thread already flagged, which we
make precise.** Buzzard anticipated it, distinguishing a curve's *actual genus*
from the *AI genus* a solver fills in, and noting the sorries only force "an
injective holomorphic map … **whether it's the Jacobian or not**; in fact I
suspect that the Jacobian is the easiest example" (Zulip, 2026-04-19) — he did not
claim the 24 are categorical. Our contribution is to pin the gap down with a
machine-checked counterexample and to formalize the repair — the universal
property, which **Michael Stoll** and **Christian Merten** proposed in that same
thread.

Buzzard's instance bundle forces `Jacobian X` to be a compact connected complex
Lie group of dimension `genus X` — i.e. a complex torus `ℂ^g/Λ` — and the
injective, holomorphic, functorial Abel–Jacobi structure kills the cheap hacks.
But the 24 leave a gap: **`genus` is pinned only at zero.**
`genus_eq_zero_iff_homeo` constrains only where `genus` *vanishes*; nothing equates
`genus X` with the true genus for `genus ≥ 1`. Since `n ↦ 2n` preserves "= 0",
the **genus-doubling object**

> `genus₂ X := 2·genus X`,  `Jacobian₂ X := Jacobian X × Jacobian X`,
> `ofCurve₂ :=` diagonal,  `pushforward₂ / pullback₂ :=` componentwise,
> `degree₂ := degree`

satisfies **every one of Buzzard's 24** yet is a `2g`-dimensional torus, not
isomorphic to the genuine `g`-dimensional Jacobian when `g > 0`. This is
machine-checked in
[`docs/categoricity/GenusDoublingCounterexample.lean`](docs/categoricity/GenusDoublingCounterexample.lean)
(`lake env lean`, exit 0): all seven instances, `genus₂_eq_zero_iff_homeo`, the
Abel–Jacobi lemmas, the four functoriality laws, `pushforward₂_pullback`, and the
capstone `genus₂_ne_genus`. So the literal 24, on their own, do not pin the
Jacobian up to isomorphism.

**Two ways to close the gap; we formalize one of them.** Full argument with the
Gemini deep-think vet in
[`docs/categoricity/CATEGORICITY_24_VS_ALBANESE.md`](docs/categoricity/CATEGORICITY_24_VS_ALBANESE.md),
both repairs formalized in
[`docs/categoricity/Condition25.lean`](docs/categoricity/Condition25.lean):

- **Condition 25 — pin `genus`** to the analytic genus
  `finrank ℂ (HolomorphicOneForm X)` (`GenusEquality`). This is exactly what the
  counterexample violates (`genusDoubling_violates_condition25`), and **our own
  construction satisfies it definitionally** (`repo_satisfies_condition25 := rfl`,
  since we *define* `genus := finrank H⁰(Ω¹)`) — so our Jacobian is the genuine
  one, not the doubling object. With Condition 25 the 24 *are* categorical
  *conjecturally* — `T(X) ≅ J(X)` for all `X` would follow from a
  Chow-motive + Brill–Noether rigidity result (the load-bearing input is
  `ofCurve_inj`, vindicating Buzzard's design). That result is non-elementary and
  unproved here; `Condition25.lean` records it as `RigidityClaim` — an unproven
  proposition threaded as an explicit hypothesis, deliberately **not** an `axiom`
  (an unproven claim must never silently extend the kernel).
- **Albanese universality** — require `(Jacobian X, ofCurve x₀)` to be the
  **initial** pointed holomorphic map from `X` to complex tori. By Yoneda an
  initial object is unique up to unique isomorphism, so this pins the Jacobian as
  a pointed torus, repairs the genus gap in one stroke, and turns the degree
  identity `f_* ∘ f^* = deg·id` into a *consequence* rather than a separate axiom.
  It is the clean, *constructively formalizable* certificate of the same
  categoricity — which is why we build it rather than the motivic rigidity proof.

This repo encodes the second. `IsJacobian`
([`Jacobians/UniversalProperty.lean`](Jacobians/UniversalProperty.lean)) is the
Albanese property quantified over complex tori of any dimension. **Categoricity
itself is axiom-free**: `isJacobian_unique` proves any two objects satisfying the
property are uniquely biholomorphically isomorphic (standard-3, using none of
Buzzard's 24 — PR #246). Our concrete construction satisfies the property via
`ofCurve_isJacobian`, which now carries only **AK** (`AX_curve_image_subgroup_isOpen`):
the three legacy Albanese-torus axioms were discharged/escaped in PR #253 (G3 proved; A1
moved out of the closure via the presented-torus typeclass reframe). Discharging AK
(a ~25-decl Kirov port) is the remaining endgame. Full status, the two-level "what it takes
to pin the Jacobian" tradeoff, and the step-by-step AK-from-Kirov proof bridge:
[`docs/planning/UNIFIED_ALBANESE_DISCHARGE_PLAN.md`](docs/planning/UNIFIED_ALBANESE_DISCHARGE_PLAN.md)
(→ [`ALBANESE_REPOINT_REFACTOR.md`](docs/planning/ALBANESE_REPOINT_REFACTOR.md),
[`A1_THINNING_PLAN.md`](docs/planning/A1_THINNING_PLAN.md)).

Credit for the universal-property repair belongs to the challenge thread:
**Michael Stoll** raised it first (2026-04-19, "to make sure no hacks are
possible", including the **complex-tori** formulation we use), and **Christian
Merten** built it into an algebraic-geometry variant (`exists_unique_ofCurve_comp`,
2026-04-20). We reached the complex-analytic formalization (`IsJacobian`)
independently, but they proposed the idea first.

## What this repo proves

Genuine theorems — what a reader can trust the formalization to have established
(modulo the axioms each names; `#print axioms`-checked, no `sorryAx`):

| Result | Status |
|--------|--------|
| `genus ProjectiveLine = 0` | **axiom-free** (chart-cocycle + Liouville: 1-forms on ℙ¹ are a subsingleton) |
| `genus (Elliptic ω₁ ω₂) = 1` | **axiom-free** (intrinsic Liouville on `ellipticDz`) |
| `genus (HyperellipticEven H) = deg(f)/2 − 1` | **axiom-free** (Liouville L2/L3 discharged) |
| Abel–Jacobi **injective** for genus > 0 | **theorem** — `ofCurve_inj`, **standard-3** (axiom-free; via the proved T-GEN + basis-free Abel engine, PR #251) |
| Abel's theorem (`AX_AbelTheorem`) | **theorem** — Forster §20 ∂̄-engine (⊆) + Liouville/Jacobi pencil (⊇) |
| `genus_eq_zero_iff_homeo` | **axiom-free** (RR pole extraction → degree-1 map → S²; backward via π₁(S²)=1 + Liouville) |
| Riemann–Roch + Serre duality | **theorems** over the Layer-3 cohomology tower (standard-3) |
| Albanese **categoricity** `isJacobian_unique` | **axiom-free** (standard-3) — any two objects satisfying the universal property are uniquely biholomorphically isomorphic; uses none of Buzzard's 24 (PR #246) |
| ↳ our construction satisfies it `ofCurve_isJacobian` | **theorem** — standard-3 + AK only (the 3 torus axioms discharged/escaped, PR #253) |
| Functoriality identities (push/pull id + comp, degree) | derived **theorems** |

### Explicit curves — concrete, axiom-clean validation

Abstract definitions can be degenerate and still compile; concrete instances catch
that. We instantiate the whole pipeline (chart-local 1-forms → genus → Jacobian →
functoriality) on real curve families and check the headlines are
`#print axioms`-clean:

- **`ProjectiveLine`** — `genus = 0`, axiom-free.
- **`Elliptic ω₁ ω₂`** — `genus = 1`, axiom-free; the Abel-injectivity witness
  `elliptic_ofCurve_injective` is proved directly on `ℂ/Λ` through the period
  lattice; and **`ellipticPeriodCycleBasis`** is a fully unconditional
  (standard-3) witness of the `AX_PeriodCycleBasis` *content* at `g = 1` — the
  first positive-genus instantiation of the (now headline-discharged) axiom's
  content.
- **`HyperellipticEven` / `HyperellipticOdd`** — the genus-`g` family `y² = f(x)`
  for squarefree `f`, the repo's **deepest end-to-end test**, built from the ground
  up:
  - a real type carrying Buzzard's full **complex-manifold structure** — the
    two-sheeted affine atlas glued to a chart at infinity (`EvenAtlas` / `OddAtlas`,
    the latter's infinity chart discharged in PR #183) — reducing to **standard-3**;
  - the **canonical holomorphic 1-form basis** `{x^k dx/y : k < g}`
    (`hyperellipticEvenBasisDifferential`), the classical differentials of the
    first kind, constructed and proved holomorphic;
  - the **genus formula** `genus = deg(f)/2 − 1` as a proved, **axiom-free**
    theorem over the *whole* even-degree family (`genus_HyperellipticEven_eq`).

  As a cross-check, **"genus 1" comes out identically from three independent
  constructions** — `Elliptic`, `HyperellipticOdd` at `deg 3`, and
  `HyperellipticEvenProj` at `deg 4` — all axiom-free. The example drives the entire
  pipeline (chart-local 1-forms → cocycle → finite-dimensionality → genus) on a
  nontrivial positive-genus family, forcing the *general* `genus` definition to
  compute the right number, not just typecheck. The odd-degree track mirrors the
  even one decl-for-decl (genus **fully discharged**, PR #223). Building on that, a **cycle basis
  + explicit period map** on the odd hyperelliptic family — which would discharge
  `AX_PeriodCycleBasis` there and give an explicit map from moduli (the branch points of `f`) to
  period matrices in the Siegel upper half space — is largely scaffolded; the route to finish it is
  in [`docs/planning/HYP_PERIOD_MAP_PLAN.md`](docs/planning/HYP_PERIOD_MAP_PLAN.md) (gap ledger:
  [`HYP_CB_BLOCKER.md`](docs/planning/HYP_CB_BLOCKER.md)).
- **`PlaneCurve`** — smooth plane curves with a fully proved manifold structure.

Each curve's headline is `#print axioms`-clean — concrete, positive-genus
evidence that the general definitions are non-vacuous, independent of the axiom
layer.

## How the work divides — three separable parts

| Part | What it is | Required for the challenge? |
|------|-----------|:---:|
| **1. Buzzard's challenge** — `Challenge.lean` + the construction | the interface Buzzard posed | — *(it **is** the challenge)* |
| **2. The RR/Serre tower** — `Layer3/`, `RiemannSurface/Cohomology/` | prove the deep axioms instead of assuming them | no — the challenge *rests on* the axioms; this *discharges* them |
| **3. Explicit-curve projects** — `ProjectiveCurve/`, `Extensions/` | exercise the formalization on real curves | no — validation |

**Part 1 is closed and axiom-free**: all 24 `sorry`s filled, the anti-degeneracy
headlines proved, and every headline `#print axioms`-checks to the three standard
Lean axioms (the last challenge-critical axiom, `AX_PeriodCycleBasis`, was
discharged from every headline closure — PRs #248/#250/#251). In Buzzard's terms
("sorry-free ⇒ done"), Part 1 is met.

**Part 2** reduces the challenge toward a single classical spine. Riemann–Roch and
Serre duality are **theorems** (`riemannRochL3`, `serreDualityL3`, standard-3) over
a thin cohomology scaffold — the **Layer-3 tower** — built on the Kirov Dolbeault
port's Čech `H¹` and skyscraper long exact sequence. Everything the 24 obligations
rest on has now been discharged from the headline closures; the discharge
timeline is in [`docs/history.md`](docs/history.md).

**Part 3** is orthogonal validation — the explicit curves above.

## How it's built

The construction takes the **period-lattice route** —
`Jac X = (HolomorphicOneForm X)* / H₁` — rather than the symmetric product
`Xᵍ/Sᵍ` (whose coincident-point analysis Buzzard flags as hard). It is basis-free
at the type level.

- **`AbelianVariety/`** — `ComplexTorus V L := V ⧸ L` for a ℤ-lattice `L`,
  supplying all 7 typeclass instances Buzzard requires on `Jacobian X` from a
  translation atlas + lattice discreteness. **Axiom-free.**
- **`RiemannSurface/` + `Jacobian/`** — Buzzard's typeclasses → holomorphic
  1-forms → period lattice → `Jacobian X`. The Abel–Jacobi map is a real `∫`, a
  multi-chart line integral over an analytic cycle basis.
- **`ProjectiveCurve/`** — real curve `def`s satisfying Buzzard's typeclasses by
  construction (the explicit curves above).
- **`Layer3/` + `RiemannSurface/Cohomology/`** — the RR/Serre tower (Part 2).
- **`Extensions/`** — end-to-end test theorems on the curve families.

## `AX_PeriodCycleBasis` — discharged from the headlines

`AX_PeriodCycleBasis` (in [`Jacobians/Axioms/PeriodCycleBasis.lean`](Jacobians/Axioms/PeriodCycleBasis.lean))
was the last challenge-critical axiom: every compact connected Riemann surface of
genus `g` admits `2g` piecewise-analytic loops whose periods generate a
**discrete, non-degenerate lattice** in `ℂ^g` (plus Riemann's bilinear relations
as `R1`/`R2` fields). The Buzzard-critical content is only the lattice's
discreteness and non-degeneracy. Classical: Forster §§19–21.

**It is no longer in any headline's closure** (PRs #248/#250/#251). The two global
period-lattice instances were reproved from the **unconditional T-GEN theorem**
`analyticLoopsGenerateH1` — *analytic loops generate H₁*, proved standard-3 via
piecewise-linear-in-charts approximation (#248) — and the `ofCurve_inj` headline
was rerouted through the basis-free Abel engine; a ℙ¹-instance unification (#250)
removed the chart diamond that blocked the rewiring. The `g = 1` content was
already a fully unconditional witness (`ellipticPeriodCycleBasis`, standard-3).

The axiom **remains declared** (so the kernel axiom count is still 10) only as
scaffolding for the non-headline R1/R2 (Riemann bilinear relations) story and the
cycle-basis witnesses — *deleting* it from the repository would additionally need
R1/R2 in full generality (genuine unformalized Hodge content, proved so far only
for `g ≤ 1` / elliptic / hyperelliptic). Every active axiom is off the Buzzard
headline path; all are classified in [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) with
per-axiom discharge plans under [`docs/planning/`](docs/planning/).

## Follow-up directions

None of these are required for the challenge; they are natural next steps the
scaffolding already sets up.

- **Finish the Albanese proof (the validation endgame).** Categoricity of the
  universal property — `isJacobian_unique`, that *any* two objects satisfying it
  are uniquely isomorphic — is already axiom-free. What still rests on axioms is
  that *our* construction satisfies the property (`ofCurve_isJacobian`), which now rests
  on a single curve-side axiom AK (`AX_curve_image_subgroup_isOpen`) — the three legacy
  torus axioms were discharged/escaped (PR #253). Discharging AK makes the full certificate —
  "our Jacobian is *the* Jacobian, up to unique isomorphism" — axiom-free, the
  strongest validation the construction can carry.
- **Explicit hyperelliptic Jacobians.** The Jacobian of a hyperelliptic curve is
  already constructed (the general construction applies, and the extension files
  force `genus`/`Jacobian`/`ofCurve`/`pushforward`/`pullback` to fire on the
  concrete type). The **odd** parity goes further: it carries explicit period
  machinery — branch-cut cycle loops and their period vectors
  (`Hyperelliptic/{CycleLoops,BoundaryWord,CycleBasisWitness}.lean`) — assembled
  into a `PeriodCycleBasis` witness that is currently *conditional* on a branch-cut
  datum. Finishing it unconditionally, and reading off the explicit **period
  matrix** `∫_{cycle} x^k dx/y`, would give a concrete, computed Jacobian for the
  whole odd family — the higher-genus analogue of `ellipticPeriodCycleBasis`
  (already unconditional at `g = 1`, `ℂ/Λ` with explicit generators). Note the
  even/odd split: the **even** parity leads on the *genus* formula (proved,
  axiom-free) but its period side is the follow-up twin
  (`periodLattice_rank_HyperellipticEven_eq`, currently a `sorry` scaffold) — the
  odd model's single point at infinity gives the cleaner branch-cut homology, so
  the explicit period work landed there.
- **The principal polarization and Torelli.** The universal property pins the
  Jacobian as a *pointed torus*, not yet as a principally polarized abelian
  variety. The polarization is canonically derivable — push the curve's
  intersection form on `H₁` forward along the forced `aj_*` isomorphism — which
  gives the theta divisor and, in principle, Torelli (the curve is recoverable from
  its ppav). A natural deepening beyond the challenge's notion of "Jacobian".
- **Independence — our own RR/Serre.** The analytical engine is currently the
  vendored Kirov Dolbeault port. Reproving Riemann–Roch and Serre duality in our
  own formulation (ideas from the port, implementation ours) would make the
  Layer-3 tower independent of that dependency.
- **Loose ends** — the odd-degree genus upper bound (the twin of the proved even
  formula), and explicit periods for the plane-curve family.

## Contributors & acknowledgments

An agent-assisted community project: collaborators' AI agents do most of the work
under light human steering, coordinated through GitHub PRs. Contributions span
code, vendored proofs, and the issue/triage layer.

- **[Michael R. Douglas](https://github.com/mrdouglasny)** — project lead;
  scaffold, axiom layer, curve theory, and the Abel engine.
- **[daouid](https://github.com/daouid)** — the Abel–Jacobi functoriality cluster
  and period-lattice comparison, the period bilinear-relations route, and the
  odd-atlas infinity-chart cluster (PR #183).
- **[sqrt-of-2](https://github.com/sqrt-of-2)** — topology and discharge PRs.
- **Jack McCarthy ([@Deicyde](https://github.com/Deicyde))** — the axiom-discharge
  issue tracker ([#77](https://github.com/mrdouglasny/jacobian-challenge/issues/77))
  that structures the open-problem surface, and the Abel–Jacobi smoothness
  discharge (PR #179).
- **Rado Kirov ([@rkirov](https://github.com/rkirov))** — produced the first
  **complete, sorry-free, axiom-free** formalization of the challenge (his repo is
  verified sorry-free with zero custom axioms, commit `cd16360`, 2026-06-13), and
  generously released it under **Apache 2.0** so others could build on it directly.
  We did. **His Dolbeault library is a load-bearing dependency here:** the ~86k-LOC
  port ([`vendor/kirov-dolbeault-port/`](vendor/kirov-dolbeault-port/),
  forward-ported to our Mathlib in a 6-edit lift) supplies the analytical engine —
  Čech cohomology, the residue theorem, Riemann–Roch and Serre duality — on which
  our Layer-3 RR/Serre tower and Abel ∂̄-engine rest. His finished proof is the
  benchmark for this problem and the **first** existence proof that it is fully
  formalizable in current Lean; our contribution is complementary (explicit curves, the
  categoricity analysis, a different construction), not a competitor. We also owe
  him a key idea for our endgame: discharging the period-lattice axiom
  **non-constructively** — span all closed loops and prove the lattice is discrete
  and non-degenerate, so Mathlib's `ZLattice` theory yields its full rank `2g` *by
  existence*, with no explicit basis of 1-cycles (which would have required
  real-analytic approximation theorems Mathlib lacks). Smaller verbatim modules are
  vendored under `Jacobians/Vendor/Kirov/`.
- **Michal Wallace ([@tangentstorm](https://github.com/tangentstorm))** — six
  self-contained analytic modules (holomorphic maps, meromorphic order, branched
  covers, cotangent bundle), each **sorry-free and axiom-free** and cleanly
  reusable — released under **MIT**, vendored under `Jacobians/Vendor/Wallace/`,
  and used in the genus-obstruction proof behind Abel injectivity. An independent
  Challenge attempt whose decoupled analytic layer we were glad to build on.
- **Kevin Buzzard** — the challenge.

External AI reviewers — **Gemini** (deep-think axiom vetting: type, strength,
non-vacuity, satisfiability for every project axiom) and **Codex / GPT-5.4**
(rescue passes and proof-strategy review).

> GitHub's *Contributors* graph counts commits only; issue, review, and
> vendored-code contributions are credited here. A numerical contribution
> breakdown (LOC + PRs by author and source) is in
> [`docs/history.md`](docs/history.md).

## Vendored sources & attribution

Real Lean from two sibling Challenge attempts, each vendored under its upstream
license with per-file attribution headers, the upstream `LICENSE`, and a
`PROVENANCE.md`. Full record: [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md).

- **[rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude)** (Apache 2.0)
  — see [Contributors](#contributors--acknowledgments). In-build subtree
  `Jacobians/Vendor/Kirov/`, plus the larger `vendor/kirov-dolbeault-port/` — a
  forward-port committed in our tree and built as a local Lake package (a
  path-based `require`, not a remote dependency).
- **[tangentstorm/JacobianChallenge](https://github.com/tangentstorm/JacobianChallenge)** (MIT)
  — `Jacobians/Vendor/Wallace/`.

The in-build vendored subtrees are **axiom-free**; their headline theorems
`#print axioms`-verify to the three standard Lean axioms only.

## Caveats

- **The axioms are AI-authored and not human-reviewed.** Each was written or
  curated in-session and cross-vetted by a second model (Gemini deep-think +
  Codex), but none has had independent human-mathematician review. If you are
  evaluating this work, read [`Jacobians/Axioms/`](Jacobians/Axioms/) and
  [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) first.
- **Axiom-free headlines still rest on the vendored engine.** The 24 headlines are
  `#print axioms` standard-3, but a large share of the proof weight lives in the
  vendored Kirov Dolbeault port (residue theorem, Čech `H¹`, Serre duality) — real
  Lean, but not *our* from-first-principles development. Read "axiom-free" as
  *"reduced to the core Lean axioms over a trusted vendored analytical engine"*,
  not *"reproved from Mathlib alone"*. (And the broader repo still declares 10
  axioms off the headline path — see `AXIOM_AUDIT.md`.)
- **Zero human-written Lean.** The Lean was written by AI agents (primarily
  Claude, with Codex rescue passes and Gemini audits), directed by a mathematician
  on scope, the axiom-vs-proof boundary, and review of every landing.
- **Remaining `sorry`s** are all off the challenge path: a handful in the
  out-of-scope `Extensions/` stretch projects and an optional adelic `H¹`
  construction kept around as a candidate deeper discharge.

## Building

```bash
lake build
```

Lean `v4.30.0`; Mathlib at the revision pinned in `lake-manifest.json`. CI runs
the full build, a `ChallengeConformance.lean` machine-check (every v0.4 signature
restated as an `example` and discharged by our decls), a golden `#print axioms`
diff, and a guard keeping the core `sorry`-free.

## Comparator verification

The [Lean FRO comparator](https://github.com/leanprover/comparator) is a
trustworthy external judge: it compiles the challenge and solution files in
sandboxes, replays the solution through the Lean kernel, and confirms the proved
theorems prove the *same statements* as the challenge while using **only a
whitelisted axiom set**. Unlike our own CI, it is an independent tool — the
strongest external certificate of the kernel-and-axiom story.

- **Verified now:** `Jacobians.Layer3.riemannRochL3` at commit `67af290`, whitelist
  `propext` / `Quot.sound` / `Classical.choice` (comparator output: "Your solution
  is okay!").
- **Now unblocked:** a full **24-obligation run** — `Challenge.lean` /
  `Solution.lean` / `config-buzzard.json` in the sibling
  `jacobian-challenge-comparator-run/` — that certifies every Buzzard headline
  depends only on the standard three Lean axioms. With `AX_PeriodCycleBasis`
  discharged from every headline closure (PR #251), it now runs against `main`.

This complements the in-repo CI gate: CI catches axiom/`sorry` drift on every
push; the comparator gives an independent, kernel-level certificate at a pinned
commit.

### lean-eval leaderboard

The solution is also submitted to the Lean FRO
**[lean-eval](https://leanprover.github.io/lean-eval-leaderboard/)** benchmark
`jacobian_challenge_diffgeo` — an independent CI that fetches the source, builds
it, and replays the headline theorems through the kernel against a whitelisted
axiom set. The exact evaluated source is pinned at the immutable tag
**[`lean-eval-submission`](https://github.com/mrdouglasny/jacobian-challenge/tree/lean-eval-submission)**
(commit `2248fdf`): a self-contained, vendored workspace under
`submission/jacobian_challenge_diffgeo/` that builds clean against Mathlib
`v4.30.0` (Lean `v4.30.0`), with the 11 Buzzard property theorems depending only
on the standard three Lean axioms.

## Repository map

| Path | Contents |
|------|----------|
| [`Jacobians/Challenge.lean`](Jacobians/Challenge.lean) | Buzzard's v0.4 statements, all 24 `sorry`s closed downstream |
| [`Jacobians/ChallengeConformance.lean`](Jacobians/ChallengeConformance.lean) | machine-check against the pinned spec |
| [`Jacobians/AbelianVariety/`](Jacobians/AbelianVariety/) | `ComplexTorus` (axiom-free) |
| [`Jacobians/RiemannSurface/`](Jacobians/RiemannSurface/) | period lattice, line integrals, cohomology anchors |
| [`Jacobians/Layer3/`](Jacobians/Layer3/) | the RR/Serre cohomology tower |
| [`Jacobians/ProjectiveCurve/`](Jacobians/ProjectiveCurve/) | the explicit curves |
| [`Jacobians/UniversalProperty.lean`](Jacobians/UniversalProperty.lean) | `IsJacobian` + the Albanese categoricity theorem |
| [`Jacobians/Axioms/`](Jacobians/Axioms/) | the classified axiom layer |
| [`Jacobians/Vendor/`](Jacobians/Vendor/) | ported Kirov + Wallace modules |
| [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) | **canonical axiom audit** — start here to review the debt |
| [`docs/history.md`](docs/history.md) | the axiom-discharge timeline + contribution breakdown |
| [`docs/categoricity/`](docs/categoricity/) | the categoricity analysis, genus-doubling counterexample, and Condition 25 |

## Further reading

- [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) — kernel-verified per-axiom audit.
- [`docs/FAITHFULNESS.md`](docs/FAITHFULNESS.md) — the informal↔formal
  correspondence for every object (*"do the statements mean the mathematics"* —
  the faithfulness layer of validation).
- [`docs/VALIDATION.md`](docs/VALIDATION.md) — the acceptance argument: definition
  + anti-vacuity subset + universal property (*"did we build the right thing"*).
- [`docs/axiom-report.txt`](docs/axiom-report.txt) — golden `#print axioms` trace.
- [`docs/history.md`](docs/history.md) — discharge timeline + contributor metrics.
- [`docs/planning/`](docs/planning/) — per-axiom discharge plans.
- [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md) — what we took from
  the sibling repos.
- [`formalization.yaml`](formalization.yaml) — the mathlib-initiative self-report.

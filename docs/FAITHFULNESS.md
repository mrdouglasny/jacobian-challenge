# FAITHFULNESS — the informal ↔ formal correspondence

A self-contained certificate that the Lean formalization *faithfully transcribes* the
construction of the Jacobian of a compact Riemann surface. For each **primary object** we
give the informal definition and its exact Lean form; for each **headline statement** we
give the informal claim, the Lean theorem, a one-line proof idea, and status.

This is the **faithfulness** layer of *validation* — *"do the formal statements mean what
the mathematics means"*. The two adjacent concerns live elsewhere:
**verification** — *"are the proofs valid relative to explicit assumptions"* — is the kernel
check (`lake build`) plus the axiom certificate in
[`axiom-report.txt`](axiom-report.txt) / [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md); and the
**characterization / acceptance** argument — *"did we build the right thing"*, up to
categoricity — is in [`VALIDATION.md`](VALIDATION.md).

*(Terminology: this document was formerly titled `VERIFICATION.md`. Under the standard
V&V split, the informal↔formal correspondence is a* validation *activity — it concerns
meaning, not proof-validity — so "verification" is reserved here for the kernel/axiom
check.)*

**Status legend:** ✓ = proved and `lake build` succeeds. Axiom-clean items have
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); items marked
"+ ⟨axiom⟩" name the additional documented classical axioms they use. **As of PR #251 every
Buzzard headline is axiom-clean** — machine-checked golden trace in
[`axiom-report.txt`](axiom-report.txt) (CI-diffed). Carrier throughout: a compact connected
Riemann surface
`{X} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`.

---

## Sources & cross-reference

**Primary sources.** O. Forster, *Lectures on Riemann Surfaces* (GTM 81) — §§16–21 (Riemann–Roch,
Serre duality, Abel's theorem, the period lattice); P. Griffiths & J. Harris, *Principles of
Algebraic Geometry*, Ch. 2 (periods, Riemann bilinear relations); the challenge spec is
[Buzzard's `Challenge.lean`](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9) v0.4.

| Object / statement | Reference | Our Lean |
|---|---|---|
| `HolomorphicOneForm` (I.1) | Forster §9 / GH Ch. 0 (chart-cocycle form of `Ω¹`) | `RiemannSurface/OneForm.lean:173` |
| `genus = finrank ℂ H⁰(Ω¹)` (I.2) | Forster §17 (`g = dim H⁰(Ω¹)`) | `RiemannSurface/Genus.lean:39` |
| period lattice `Λ` (I.3) | Forster §21; GH Ch. 2 §2 | `Axioms/PeriodLatticeBase.lean` |
| `ComplexTorus V L = V ⧸ L` (I.4) | GH Ch. 2 §6 | `AbelianVariety/ComplexTorus.lean:15` |
| `Jacobian X = (Ω¹)* / Λ` (I.5) | Forster §21; GH Ch. 2 §7 | `Jacobian/Construction.lean:146`, `Challenge.lean:86` |
| Abel–Jacobi `ofCurve` (I.6) | Abel 1829; Forster §21 | `Challenge.lean:135` |
| `pushforward` / `pullback` (I.7) | functoriality of `J(-)` | `Challenge.lean:158,184` |
| `genus ℙ¹ = 0` (V.1) | classical | `ProjectiveCurve/Line/Genus.lean:29` |
| `genus (Elliptic) = 1` (V.2) | classical | `ProjectiveCurve/Elliptic/OneForm.lean:195` |
| `genus (HyperellipticEven) = deg f/2 − 1` (V.3) | classical (`y²=f(x)`) | `Extensions/HyperellipticEven.lean:161` |
| Abel–Jacobi injective, `g>0` (V.4) | Abel's theorem | `Challenge.lean:140` (`ofCurve_inj`) |
| `genus_eq_zero_iff_homeo` (V.5) | uniformization at `g=0` | `Challenge.lean:75` |
| Riemann–Roch / Serre duality (V.6) | Forster §16–17 | `Layer3/Cohomology.lean:181,195` |
| Albanese categoricity (V.7) | Yoneda / universal property | `UniversalProperty.lean:947` (`isJacobian_unique`) |
| genus-doubling **counterexample** (V.8) | the 24 are not categorical | `docs/categoricity/GenusDoublingCounterexample.lean:175` |

---

## Part I — Primary objects

### 1. Holomorphic 1-forms `H⁰(X, Ω¹)`
*Informal.* The ℂ-vector space of global holomorphic 1-forms on `X` — a section assigns to each
chart a holomorphic coefficient `coeff x : ℂ → ℂ`, transforming on overlaps by the derivative of
the chart transition (the cotangent cocycle), and vanishing off each chart target.
*Formal* (`RiemannSurface/OneForm.lean`):
```lean
abbrev HolomorphicOneForm (X) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :=
  -- ℂ-submodule of (coeff : X → ℂ → ℂ) satisfying:
  --   IsHolomorphicCoeffFamily ∧ SatisfiesCotangentCocycle ∧ IsZeroOffChartTarget
```
An `AddCommGroup` + `Module ℂ`; `coeff` / `coeff_zero` / `ext_of_coeff` are the API. ✓

### 2. Geometric genus
*Informal.* `g := dim_ℂ H⁰(X, Ω¹)` — the standard analytic genus.
*Formal* (`RiemannSurface/Genus.lean:39`):
```lean
noncomputable def genus (X) [..] : ℕ := Module.finrank ℂ (HolomorphicOneForm X)
```
This is the **anti-hack anchor**: because `genus` is *defined* as `finrank H⁰(Ω¹)`, the repo
satisfies "Condition 25" (`genus = analytic genus`) **definitionally** — the genus-doubling
counterexample (V.8) is the object that violates it. ✓

### 3. The period lattice `Λ`
*Informal.* Integrating the `2g` homology cycles against a basis of 1-forms embeds `H₁(X,ℤ)` as a
full rank-`2g` lattice `Λ ⊂ (H⁰(Ω¹))* ≅ ℂ^g` — discrete and of full real rank.
*Formal* (`Axioms/PeriodLatticeBase.lean`, instances in `Axioms/PeriodLattice.lean`):
```lean
def periodMapInBasis (X) (x₀) (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) : H1 X x₀ →+ (Fin (genus X) → ℂ)
def periodLatticeInBasis (X) (x₀) (b) : Submodule ℤ (Fin (genus X) → ℂ) := AddMonoidHom.range …
instance instPeriodLatticeDiscrete : DiscreteTopology (periodLatticeInBasis X x₀ b)   -- standard-3 (T-GEN)
instance AX_PeriodLattice          : IsZLattice ℝ (periodLatticeInBasis X x₀ b)        -- standard-3 (T-GEN)
```
Both instances are **axiom-clean** — reproved from the unconditional T-GEN theorem
`analyticLoopsGenerateH1` (PR #248/#251), no longer from `AX_PeriodCycleBasis`. ✓

### 4. Complex torus
*Informal.* For a ℤ-lattice `L ⊂ V`, the quotient group `V/L`; with `L` discrete of full rank it is
a compact complex Lie group.
*Formal* (`AbelianVariety/ComplexTorus.lean:15`):
```lean
def ComplexTorus (V) [..] (L : ZLattice) : Type _ := V ⧸ L.toAddSubgroup
```
Supplies all 7 of Buzzard's typeclass instances from a translation atlas + lattice discreteness.
**Axiom-free.** ✓

### 5. The Jacobian
*Informal.* `J(X) = (H⁰(X,Ω¹))* / Λ` — the dual of the 1-forms modulo the period lattice; a
`g`-dimensional complex torus.
*Formal* (`Jacobian/Construction.lean:146`, surfaced as `Challenge.lean:86`):
```lean
noncomputable abbrev Jacobian (X) [..] := ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X x₀ b)
```
The 7 Buzzard instances (`T2Space`, `CompactSpace`, `ConnectedSpace`, `ChartedSpace ℂ`,
`IsManifold`, `LieAddGroup`, `AddCommGroup` on `Jacobian X`) are all **axiom-clean** (post-PR #251;
they were the route by which `AX_PeriodCycleBasis` used to enter). ✓

### 6. The Abel–Jacobi map `ofCurve`
*Informal.* Fixing a basepoint `P`, `ofCurve P : X → J(X)`, `Q ↦ [ω ↦ ∫_P^Q ω]` — a genuine path
integral of 1-forms, well-defined modulo periods.
*Formal* (`Challenge.lean:135`):
```lean
noncomputable def ofCurve (P : X) : X → Jacobian X := …   -- ofCurveImpl: developing-value period map
```
A real `∫` (multi-chart line integral), not a stub. ✓

### 7. Functoriality
*Informal.* A holomorphic `f : X → Y` induces `f_* : J(X) → J(Y)` (pushforward) and
`f^* : J(Y) → J(X)` (pullback), with `f_* ∘ f^* = deg(f)·id`.
*Formal* (`Challenge.lean:158,184`): `pushforward f`, `pullback f`, `degree f`. ✓

### 8. The Albanese / Jacobian universal property (categoricity)
*Informal.* `J(X)` is the **initial** object among pointed holomorphic maps from `X` to complex
tori: every pointed holomorphic `f : X → A` (into a *presented* torus `A`) factors **uniquely**
through the Abel–Jacobi map by a holomorphic group hom. Hence any two objects with this property are
canonically isomorphic — the Jacobian is pinned up to unique isomorphism.

*Formal — the property* (`UniversalProperty.lean:108`, `IsJacobian`):
```lean
structure IsJacobian (x₀ : X) {g} (J) [..torus instances on J..] (aj : X → J) : Prop where
  aj_holo  : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin g → ℂ) ω aj
  aj_base  : aj x₀ = 0
  universal : ∀ {m} {A} [..torus instances on A..] [TorusSelfAlbanesePresentation m A] (f : X → A),
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f → f x₀ = 0 →
    ∃! φ : J →+ A, ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (φ : J → A) ∧
      ∀ x, f x = φ (aj x)
```
*Formal — our construction satisfies it* (`UniversalProperty.lean:899`, `ofCurve_isJacobian`):
```lean
theorem ofCurve_isJacobian (x₀ : X) (hg : 0 < genus X) :
    IsJacobian x₀ (Jacobian X) (Jacobian.ofCurve x₀)
```
`#print axioms ofCurve_isJacobian` ⇒ **std-3 (axiom-free)** — AK was discharged in PR #255
(2026-06-16); the closure no longer lists `AX_curve_image_subgroup_isOpen`. ✓

*Formal — categoricity (V.7)* (`UniversalProperty.lean:947`, `isJacobian_unique`):
```lean
theorem isJacobian_unique (x₀ : X)
    {J₁ J₂} [..torus instances..] [TorusSelfAlbanesePresentation g₁ J₁] [TorusSelfAlbanesePresentation g₂ J₂]
    (hJ₁ : IsJacobian x₀ J₁ aj₁) (hJ₂ : IsJacobian x₀ J₂ aj₂) :
    ∃ (φ : J₁ →+ J₂) (ψ : J₂ →+ J₁),
      ContMDiff .. ω (φ : J₁ → J₂) ∧ ContMDiff .. ω (ψ : J₂ → J₁) ∧
      ψ.comp φ = AddMonoidHom.id J₁ ∧ φ.comp ψ = AddMonoidHom.id J₂ ∧
      (∀ x, aj₂ x = φ (aj₁ x)) ∧ (∀ x, aj₁ x = ψ (aj₂ x))
```
`#print axioms isJacobian_unique` ⇒ std-3 (**axiom-free**); uses none of the 24. The concrete
corollary `isJacobian_iso_jacobian` (`J₁ ≅ Jacobian X`, `:990`) is **std-3 (axiom-free)** since
PR #255 (was std-3 + AK before AK's discharge). ✓

*Completeness — two levels (honest tradeoff).* `isJacobian_unique` carries a *presentation
hypothesis on the compared objects* (`[TorusSelfAlbanesePresentation g₁ J₁] [… g₂ J₂]`) — not
intrinsic to uniqueness, but the price of the escape hatch: the universal property only accepts
*presented* targets, so to compare `J₁`,`J₂` each must be presentable. Hence:
**Level 1 (presented tori — fully axiom-free as of PR #255).** With "complex torus" = `ℂ^g/Λ` in the
standard sense, `isJacobian_unique` pins the Jacobian up to unique iso **axiom-free**, and Buzzard's
concrete `Jacobian X` pinning is now **also fully axiom-free + unconditional**: AK
(`AX_curve_image_subgroup_isOpen`) was discharged in PR #255 (@daouid), so both `ofCurve_isJacobian`
and the concrete corollary `isJacobian_iso_jacobian` are std-3.
**Level 2 (abstract tori — no presentation assumed).** The strictly stronger, presentation-free
categoricity **requires** the uniformization input `A1`/`AX_torus_exp` — to use an abstract
competitor as a target you must *derive* its presentation. Not optional for this level; it is exactly
what removes the presentation hypothesis. Full status:
[`planning/UNIFIED_ALBANESE_DISCHARGE_PLAN.md`](planning/UNIFIED_ALBANESE_DISCHARGE_PLAN.md).

---

## Part II — Validating statements

*Each is `#print axioms`-checked; the value column is the kernel verdict.*

| # | Informal claim | Lean | Proof idea | Status |
|---|---|---|---|---|
| V.1 | `ℙ¹` has genus 0 | `genus_projectiveLine_eq_zero` | 1-forms on ℙ¹ are a subsingleton (chart-cocycle + Liouville) ⇒ `finrank = 0` | ✓ **axiom-free** |
| V.2 | An elliptic curve has genus 1 | `genus_Elliptic_eq_one` | intrinsic Liouville on `ellipticDz`; `H⁰(Ω¹)` is 1-dim | ✓ **axiom-free** |
| V.3 | `y²=f(x)` has genus `deg f/2 − 1` | `genus_HyperellipticEven_eq` | canonical basis `{xᵏ dx/y}`; count holomorphic differentials | ✓ **axiom-free** |
| V.4 | Abel–Jacobi is injective for `g>0` | `ofCurve_inj` (`Challenge.lean:140`) | basis-free Abel-⊆ engine + unconditional T-GEN; period-injectivity | ✓ **standard-3** |
| V.5 | genus 0 ⇔ homeomorphic to `S²` | `genus_eq_zero_iff_homeo` | RR pole extraction → degree-1 map → `S²`; back via `π₁(S²)=1` + Liouville | ✓ **axiom-free** |
| V.6 | Riemann–Roch + Serre duality | `riemannRochL3`, `serreDualityL3` | Layer-3 cohomology tower over the Kirov Dolbeault port (Čech `H¹` + skyscraper LES) | ✓ **standard-3** |
| V.7 | Albanese categoricity | `isJacobian_unique` | any two objects with the universal property are uniquely biholomorphic (Yoneda) | ✓ **axiom-free**, uses none of the 24 |
| V.8 | the 24 do **not** pin `J(X)` | `genus₂_ne_genus` | genus-doubling object satisfies all 24 yet is `2g`-dim | ✓ **axiom-free** (a *counterexample* — see VALIDATION) |

Cross-check: **"genus 1" arises identically from three independent constructions** — `Elliptic`,
`HyperellipticOdd` (deg 3), `HyperellipticEvenProj` (deg 4) — all axiom-free, forcing the *general*
`genus` to compute the right number, not just typecheck.

---

## Subtleties to check (the reviewer crosswalk)

Misformalization is the only failure mode the kernel cannot catch, so for each headline below is the
specific place to look — where a *true* Lean statement could still fail to mean the classical claim:

- **V.1 / ℙ¹ genus 0** — confirm `HolomorphicOneForms` is genuinely `H⁰(X, Ω¹)` (a `ContMDiffSection`
  of the holomorphic cotangent bundle), so "subsingleton" is a real vanishing, not a degenerate type.
- **V.2 / elliptic genus 1** — `ellipticDz` is the honest invariant 1-form `dz`; the curve is the
  genuine `ℂ/Λ`, not a relabelled torus.
- **V.3 / hyperelliptic genus `deg f/2 − 1`** — the even-degree atlas (`Fact (¬ Odd deg)` / EvenAtlas)
  actually charts the points at infinity (the `−1` is that correction); basis `{xᵏ dx/y}` spans the
  holomorphic differentials.
- **V.4 / Abel–Jacobi injective** — `ofCurve` is the honest `periodVec ∘ smoothPath mod Λ`, not a
  trivial map; the std-3 closure rests on the basis-free Abel-⊆ engine + T-GEN with **no** hidden axiom.
- **V.5 / genus 0 ⇔ S²** — **homeomorphism, not biholomorphism**; the sphere is the *metric* `S²` in
  `EuclideanSpace ℝ (Fin 3)`.
- **V.6 / Riemann–Roch + Serre** — `lDim` is the honest `dim L(D)` (the germ-quotient kills only junk),
  `canonicalDivisor` is the real chosen Serre divisor (de-opaqued), `H¹` is genuine Čech over the Kirov
  port; where a statement quotients by germ-zero, check it is *equivalent* to the textbook form.
- **V.7 / categoricity** — `IsJacobian` is the real `∃!` holomorphic-group-hom factorization; the
  `TorusSelfAlbanesePresentation` hypothesis is exactly what scopes this to Level 1 (presented tori),
  not a vacuity.
- **V.8 / counterexample** — the genus-doubling object genuinely satisfies **all 24** obligations yet
  is `2g`-dimensional; check it does not quietly fail a hidden requirement (that is the whole point).

## Deliberate design choices (not bugs)

Conventions a reviewer will meet that are intentional. When a statement looks weaker than the
textbook's, this is usually why — check it is *equivalent*, not broken:

- **`ULift` Jacobian.** `Jacobian X` is a `ULift` of the concrete `Type 0` torus `(Ω¹)*/Λ` into the
  universe-polymorphic Buzzard signature; all group/manifold structure lives on the underlying torus.
- **Junk values off-source.** Charts / `fderiv` carry arbitrary values off their source (e.g. the ℙ¹
  junk-point `fderiv` trick); headline statements are insensitive to junk by construction.
- **`SMul ℝ ℂ` / `restrictScalars` diamond.** The manifold layer hits the real-vs-complex scalar
  diamond; we route the actions explicitly. (Kirov's repo uses a
  `backward.isDefEq.respectTransparency false` elaboration flag for the same diamond.) Elaboration-only —
  the kernel rechecks every proof without it.
- **`Fact (¬ Odd deg)` even-atlas.** Even-degree hyperelliptic curves carry the branch parity as a
  typeclass `[Fact …]` (not an explicit hypothesis) so downstream typeclass synthesis fires — a
  Lean-mechanics choice, not a math restriction.
- **Basis-free Abel / mod-Λ periods.** `ofCurve_inj` routes through the basis-free Abel engine + T-GEN
  rather than a chosen `H₁` basis (no basis-choice ambiguity); Abel–Jacobi values are defined mod Λ.
- **Axioms are documented classical inputs, not gaps.** The 7 remaining axioms are off every headline
  closure and textbook-standard (vetted for type / strength / non-vacuity / satisfiability) — not
  `sorry`s. "Axiom-clean headline" means `#print axioms` = std-3.

---

## Axiom certificate

`main` is **`sorry`-free**, and **every Buzzard headline depends only on the three standard Lean
axioms** `[propext, Classical.choice, Quot.sound]` — machine-checked in
[`axiom-report.txt`](axiom-report.txt) (regenerated by `scripts/axiom_report.lean`, CI-diffed; 0
occurrences of `AX_PeriodCycleBasis`). `scripts/check_axiom_consistency.sh` pins the kernel axiom
count at **7** (was 8 before AK's discharge in PR #255).

The 7 declared project axioms are all **off the Buzzard headline path** (none appears in any
headline closure):

| Axiom | File | Group | Role |
|---|---|---|---|
| `AX_PeriodCycleBasis` | `Axioms/PeriodCycleBasis.lean` | period / Hodge | **discharged from all headlines** (T-GEN); kept only as R1/R2 (Riemann bilinear relations) scaffolding + cycle-basis witnesses. Deleting it needs general R1/R2 (proved so far for `g ≤ 1` / ell / hyperell). |
| `AX_torus_uniformization` (A1) | `Axioms/AlbaneseInterface.lean` | Albanese | **declared but OUT of every headline closure** (presented-torus class reframe, PR #253) — the optional abstract-torus supplier; not relied on by `ofCurve_isJacobian` / `isJacobian_unique` / `isJacobian_iso_jacobian` |
| `intersectionForm` | `Axioms/IntersectionForm.lean` | polarization | the symplectic form on `H₁`; dropped from every headline closure (D2) — kept for the principal-polarization story |
| `AX_IntersectionForm_alternating` | `Axioms/IntersectionForm.lean` | polarization | law of `intersectionForm` |
| `AX_IntersectionForm_perfect` | `Axioms/IntersectionForm.lean` | polarization | law of `intersectionForm` |
| `AX_PluckerFormula` | `Axioms/PluckerFormula.lean` | concrete-curve | plane-curve degree–genus formula (validation curves only) |
| `AX_PlaneCurveAffine_connected` | `ProjectiveCurve/PlaneCurve.lean` | concrete-curve | connectivity of an affine plane curve (validation curves only) |

*Recently discharged:* **AK `AX_curve_image_subgroup_isOpen`** (was the last axiom under
`ofCurve_isJacobian`) became a **theorem** in PR #255 (@daouid, 2026-06-16) — local Jacobi
inversion assembled from the IFT period map + a chart-FTC identity + Kirov's open lattice quotient
(`#print axioms` = std-3). With it the Albanese universal-property characterization is fully
axiom-free; kernel count 8 → 7.

Every axiom is AI-authored and Gemini/Codex-vetted (type, strength, non-vacuity, satisfiability) but
**not human-mathematician reviewed** — see [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) for the per-axiom
audit and discharge plans under [`planning/`](planning/), and [`CAVEATS`](../README.md#caveats) in
the README. The vendored Kirov Dolbeault port (the analytical engine behind RR/Serre and the Abel
∂̄-engine) is itself axiom-clean: its headline theorems `#print axioms`-verify to the three standard
Lean axioms only.

---

## How to re-check this certificate

**Internal checks** (trust our own build/`.olean`s):
```bash
lake build Jacobians                                 # sorry-free, all theorems compile
lake env lean scripts/axiom_report.lean              # regenerates the golden #print axioms trace
diff <(lake env lean scripts/axiom_report.lean) docs/axiom-report.txt   # must be empty
bash scripts/check_axiom_consistency.sh              # kernel axiom count == documented (7)
```

**External re-verification** (trusts only the kernel + Mathlib + comparator + the spec —
re-exports and re-checks every proof in a fresh kernel, *not* our `.oleans`):
```bash
scripts/verify.sh                                    # RR headline; "Your solution is okay!"
scripts/verify.sh config-buzzard.json                # the 11 Buzzard property headlines
```
This runs the real [`leanprover/comparator`](https://github.com/leanprover/comparator) against
the verbatim challenge spec via the `scripts/comparator/` workspace — statement match +
permitted-axiom check (std-3) + independent kernel replay. A local pass mirrors a green
lean-eval run for `jacobian_challenge_diffgeo`. See [`scripts/comparator/README.md`](../scripts/comparator/README.md).

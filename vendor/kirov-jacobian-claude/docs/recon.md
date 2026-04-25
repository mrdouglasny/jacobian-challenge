# Mathlib Reconnaissance — Jacobians Challenge at 8e3c989

Audit of `/home/rado/jacobian/.lake/packages/mathlib/Mathlib/` at commit
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (2026-04-15) for the pieces needed
to close the sorries in `Jacobians.lean`. File paths below are relative to
`.lake/packages/mathlib/Mathlib/`.

For each sorry: what's needed, what Mathlib already provides, what's missing
and must be built, a gap estimate, and whether to build curve-only or take
the cheap Mathlib-idiomatic generalization.

> **Generality policy** (from `/docs/DESIGN.md`): curve-only by default for
> `Jacobian`, `ofCurve`, `periodLattice`, `pushforward`/`pullback` and
> `pushforward_pullback`. Generalize where it's free: holomorphic 1-forms
> (any complex manifold), topological `genus` (closed oriented 2-manifolds),
> `degree` (proper holomorphic map between equidim complex manifolds).

---

## Global infrastructure summary

What **is** in Mathlib at this commit (ready to use):

| Piece | File(s) |
|---|---|
| `ChartedSpace`, `IsManifold I n M` for `n ∈ ℕ ∪ {∞, ω}` | `Geometry/Manifold/IsManifold/Basic.lean` |
| `LieAddGroup I n G`, `LieGroup I n G` bundled classes | `Geometry/Manifold/Algebra/LieGroup.lean:62,72` |
| `instNormedSpaceLieAddGroup` — every normed `𝕜`-space is a Lie group | `Geometry/Manifold/Algebra/LieGroup.lean:197` |
| `𝓘(ℂ)` notation = `modelWithCornersSelf ℂ ℂ` | `Geometry/Manifold/Notation.lean` |
| `MDifferentiable` for complex manifolds, max modulus | `Geometry/Manifold/Complex.lean` |
| `IsZLattice K L` — discrete full-rank ℤ-submodule | `Algebra/Module/ZLattice/Basic.lean:435` |
| `ZLattice.rank`, `module_free`, `isAddFundamentalDomain` | `Algebra/Module/ZLattice/Basic.lean:526,513,647` |
| `IsZLattice.isCompact_range_of_periodic` | `Algebra/Module/ZLattice/Basic.lean:793` |
| Singular chain complex + homology functors (`ModuleCat ℤ` is abelian) | `AlgebraicTopology/SingularHomology/Basic.lean:36,54` |
| Homotopy invariance of singular homology | `AlgebraicTopology/SingularHomology/HomotopyInvarianceTopCat.lean` |
| `FundamentalGroup X x` and its maps | `AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean:35` |
| `Abelianization` of a group | `GroupTheory/Abelianization/Defs.lean:38` |
| `Sheaf.H F n` — sheaf cohomology via `Ext` (any Grothendieck site, abelian sheaves) | `CategoryTheory/Sites/SheafCohomology/Basic.lean:58` |
| Structure sheaf of smooth / analytic functions on a manifold | `Geometry/Manifold/Sheaf/Smooth.lean` |
| Exterior derivative of `n`-forms on a normed space | `Analysis/Calculus/DifferentialForm/Basic.lean` |
| `Module.Dual`, dual basis, `Module.evalEquiv` for finite-dim | `LinearAlgebra/Dual/*`, `LinearAlgebra/FiniteDimensional/Basic.lean` |
| Cauchy integral, residue theorem (`ℂ → E` circle integral) | `Analysis/Complex/CauchyIntegral.lean` |
| `HomologicalComplex.eulerChar` — Euler char of a chain complex | `Algebra/Homology/EulerCharacteristic.lean` |
| Sphere `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`, stereographic charts | `Geometry/Manifold/Instances/Sphere.lean` |
| Poincaré conjecture statements (all `proof_wanted`) | `Geometry/Manifold/PoincareConjecture.lean` |

What's **not** in Mathlib (confirmed gaps):

- `ChartedSpace` / `IsManifold` / `LieAddGroup` instance on `G ⧸ N` for a Lie
  group `G` and discrete closed normal `N`. `Topology/Algebra/Group/Quotient.lean`
  gives only the topological-group side (topology transfer, compactness,
  T1 when closed) — no manifold structure, no `T2` instance, no Lie
  structure transfer.
- Hurewicz theorem `π₁(X,x₀)ᵃᵇ ≃ H₁(X,ℤ)`. (The only `Hurewicz` grep hit is
  a stray comment in `Topology/Homotopy/Lifting.lean:295`.)
- `BettiNumber` / topological `EulerChar(X)`; only the *homological-complex*
  Euler char exists, not a canonical topological one tying to `H_n(X; ℚ)`.
- Classification of closed oriented surfaces; no `genus`-for-surfaces.
- Bundled smooth `n`-forms on manifolds (explicit TODO in
  `Analysis/Calculus/DifferentialForm/Basic.lean:36–45`). Exterior derivative
  is defined on *normed spaces only*.
- Holomorphic 1-forms on a complex manifold as a defined object (only
  `Mathlib/Geometry/Manifold/Complex.lean` exists, whose docstring explicitly
  lists sheaves of holomorphic / meromorphic functions as open TODOs).
- Line integral / path integral of 1-forms along paths on a manifold.
  `Analysis/Complex/CauchyIntegral.lean` covers the ℂ-valued circle case but
  not general 1-forms.
- Mapping degree / winding number / local degree / Brouwer degree (grep
  returns zero hits across `Mathlib/`).
- Uniformization theorem; Riemann sphere API; any Riemann-surface-specific
  theory beyond what's inherited from "complex manifold".

---

## Per-sorry audit

### `genus X` (line 43) and `genus_eq_zero_iff_homeo` (line 51)

**Math needed:** assign `ℕ` to a compact Riemann surface; for the iff,
establish the homeomorphism classification in genus 0.

**In Mathlib:** singular H₁ via `singularHomologyFunctor` applied to
`ModuleCat ℤ` gives `H₁(X, ℤ)` as an abelian group. `Module.finrank` over ℤ
gives the rank. `HomologicalComplex.eulerChar` gives χ of the singular chain
complex. Sphere type and stereographic charts are available.

**Missing (curve-only build):**
- `genus X := finrank ℤ (H₁(X, ℤ)) / 2` — build as a direct definition. Needs
  `Hn(X; ℤ)` specialized to `n = 1` and to oriented closed 2-manifolds having
  a *free* `H₁` of even rank (fact). Alternative: `(2 - χ(X)) / 2` using the
  homological Euler char on the singular chain complex over ℚ or ℝ.
- `genus_eq_zero_iff_homeo`: both directions require surface classification
  / uniformization. The → direction says "trivial H₁ on a closed oriented
  2-manifold ⇒ homeomorphic to S²" — this is uniformization (topological,
  2D Poincaré). The ← direction is easier: compute H₁(S²) = 0.

**Gap estimate:** Large. Uniformization for genus 0 alone is a substantial
theorem. H₁-of-S² is small.

**Generalization:** topological `genus` for closed oriented 2-manifolds
(cheap — same effort, makes the definition not intrinsically
complex-analytic). `genus_eq_zero_iff_homeo` stays in the Riemann-surface
setting because it relies on an analytic input (every topological surface
admits a complex structure, but that's the fact we'd use).

**Canonical ref:** Forster §14 (topological invariants); Forster §27
(uniformization for genus 0); Miranda Ch. IV §1.

---

### `Jacobian X` (line 58)

**Math needed:** a type for the Jacobian — per design,
`(H⁰(X, Ω¹_X))ᵛ ⧸ image of H₁(X, ℤ)`.

**In Mathlib:** dual of a f.d. ℂ-vector space is standard; quotient by an
`AddSubgroup` is standard (`QuotientAddGroup`); `IsZLattice` gives
discrete-full-rank lattices.

**Missing:** everything content-bearing — `H⁰(X, Ω¹_X)` (the ℂ-vector space
of global holomorphic 1-forms), the period pairing `H₁(X,ℤ) × H⁰(X,Ω¹) → ℂ`,
and a proof that its image is an `IsZLattice`.

**Gap estimate:** Very large. This pulls in holomorphic 1-forms,
path/cycle integration, and Riemann bilinear relations (to show full rank).

**Generalization:** curve-only. Albanese for compact Kähler is deferred.

**Canonical ref:** Forster §21 (holomorphic 1-forms + periods + Jacobian);
Miranda Ch. VIII §§1–3.

---

### `Jacobian X` instances (lines 65–86)

| Instance | What we need | Mathlib status |
|---|---|---|
| `AddCommGroup` (65) | from the underlying quotient | free from `QuotientAddGroup.Quotient` once the subgroup is defined |
| `TopologicalSpace` (69) | quotient topology | free from `Topology/Algebra/Group/Quotient.lean` |
| `T2Space` (72) | quotient is Hausdorff | *needs* the period lattice to be closed; `T1` lemma exists for closed subgroups, but `T2` on `G ⧸ H` requires the subgroup to be closed (→ `IsClosed (Λ : Set E)`). Closed follows from discrete in a f.d. space. |
| `CompactSpace` (75) | the quotient is compact | `IsZLattice.isCompact_range_of_periodic` (line 793) gives it essentially. |
| `ChartedSpace (Fin (genus X) → ℂ)` (80) | complex-manifold charts | **gap**: no `ChartedSpace` instance on `G ⧸ H` in Mathlib. Must be built. |
| `IsManifold 𝓘(…) ω` (83) | analytic manifold | downstream of the ChartedSpace; needs analyticity of the transition maps — follows once the charts are defined by local sections of the quotient map. |
| `LieAddGroup 𝓘(…) ω` (86) | analytic Lie group | downstream of the manifold structure; addition/negation analyticity follows from ambient `instNormedSpaceLieAddGroup` descending to the quotient. |

**Generalization:** these *instances* are the curve-only consequence of a
general "quotient of a finite-dim normed `𝕜`-space by an `IsZLattice`" Lie
group structure — a candidate for Mathlib upstream (good standalone lemma,
no Riemann-surface content). We'd build this general lemma and specialize.

**Canonical ref:** Lee, *Introduction to Smooth Manifolds*, Ch. 21 (Lie
subgroups and quotients); for the specific ℝⁿ / Λ case Forster §21 just
uses it implicitly.

**Gap estimate:** Small for 65, 69, 75. Medium for 72 (proving Λ closed).
Medium-to-large for 80 (the new Mathlib lemma). Small for 83, 86 given 80.

---

### `ofCurve P` (line 89), `ofCurve_contMDiff` (91), `ofCurve_self` (94), `ofCurve_inj` (97)

**Math needed:**
- `ofCurve P : X → Jacobian X`, `Q ↦ [ω ↦ ∫_P^Q ω]`. Requires picking a path
  from `P` to `Q`; well-defined modulo the period lattice.
- `ofCurve_self`: `ofCurve P P = 0` (trivial once well-defined).
- `ofCurve_contMDiff`: holomorphic. Locally given by integration of
  holomorphic 1-forms; locally antiderivative ⇒ holomorphic.
- `ofCurve_inj` (Abel's theorem): injective for genus > 0.

**In Mathlib:** nothing directly. Cauchy integral for circles exists; no
general-manifold line integral; no universal cover API usable for
well-definedness mod periods.

**Gap estimate:** Very large. Abel's theorem is a headline Riemann-surface
result.

**Generalization:** curve-only. (The general Kähler version — Albanese
map — is deferred.)

**Canonical ref:** Forster §20 (Abel-Jacobi map), §21 (Abel's theorem);
Miranda Ch. VIII §§1–3.

---

### `pushforward` (105), `pushforward_contMDiff` (110), `pushforward_id_apply` (115), `pushforward_comp_apply` (123); mirror for `pullback` (129, 134, 139, 142)

**Math needed:** for `f : X → Y` holomorphic between compact Riemann
surfaces, induced maps `f_* : J(X) → J(Y)` and `f^* : J(Y) → J(X)` as
continuous group homomorphisms; their holomorphicity and functoriality.

**In Mathlib:** `ContinuousAddMonoidHom` / `→ₜ+` infrastructure is present
(required for the output types). Functoriality lemmas `contMDiff_id`,
`ContMDiff.comp` are standard.

**Missing:** the constructions themselves, which require (a) functoriality
of `H⁰(Ω¹)` under holomorphic maps, (b) functoriality of `H₁` under
continuous maps (mostly free from `singularHomologyFunctor`), (c)
compatibility with the period pairing. Holomorphicity follows from
compatibility with linear maps on the finite-dim ambient spaces.

**Gap estimate:** Medium on top of `Jacobian` existing.

**Generalization:** curve-only for now (functoriality of Albanese is the
general statement).

**Canonical ref:** Miranda Ch. VII (pullback of forms, pushforward of
divisors); Griffiths–Harris Ch. 2.

---

### `ContMDiff.degree` (147)

**Math needed:** `ℕ` assigned to a holomorphic map `f : X → Y` of compact
Riemann surfaces; zero if constant, otherwise the usual degree = cardinality
of a generic fibre = degree of `f^{-1}(P)` as a divisor.

**In Mathlib:** **nothing on degree of maps.** No winding number, no local
degree, no Brouwer degree, no algebraic-intersection degree. Closest is
the residue / argument-principle infrastructure inside
`Analysis/Complex/CauchyIntegral.lean`, which implies winding but hasn't been
abstracted.

**Gap estimate:** Medium-to-large to define cleanly. A clean path: define
`localDegree` of a non-constant holomorphic germ via multiplicity of zero,
then sum over a fibre.

**Generalization:** degree for a proper holomorphic map between equidim
connected complex manifolds is the natural Mathlib-idiomatic form. Cheap to
state in that generality (the construction is the same); theorems about the
Riemann-surface case then follow.

**Canonical ref:** Forster §4 (proper holomorphic maps and degree);
Miranda Ch. IV.

---

### `pushforward_pullback` (151): `f_* ∘ f^* P = (deg f) • P`

**Math needed:** for all `P : J(Y)`, `pushforward f hf (pullback f hf P) =
(ContMDiff.degree f hf) • P`.

**In Mathlib:** nothing directly. Builds on every earlier gap.

**Gap estimate:** Medium on top of `degree`, `pushforward`, `pullback`
existing. The proof is: pullback then pushforward on 1-forms is
multiplication by degree (trace-like identity), same on `H₁`; pass to the
quotient.

**Generalization:** curve-only. The statement is intrinsically about maps
of compact Riemann surfaces (or their higher-dim Albanese analogues, which
are deferred).

**Canonical ref:** Miranda Ch. VIII §3; Griffiths–Harris §2.7.

---

## Current state (as of most recent commit)

**Challenge file `Jacobians.lean`:** 19 sorries (down from 24 at start).

**Closed so far:**
- `def Jacobian X := ...` — now the period-lattice quotient.
- Five structural instances on `Jacobian X`: `AddCommGroup`, `TopologicalSpace`,
  `T2Space`, `CompactSpace`, `ChartedSpace (Fin (genus X) → ℂ)`.
- Two more: `IsManifold` and `LieAddGroup` on `Jacobian X` — routed through
  stubs in `Jacobians/ZLatticeQuotient.lean` (documented proof sketches).

**Remaining 19 sorries break into four clusters, all gated on content:**

1. *Period lattice content* (3 sorries): `periodLattice X`, its
   `DiscreteTopology` and `IsZLattice ℝ` instances. Needs holomorphic 1-forms
   + singular H₁ + integration.
2. *Topological genus* (2 sorries): `genus`, `genus_eq_zero_iff_homeo`.
   Needs a definition (e.g. `rank(H₁(X, ℤ)) / 2`) + uniformization for genus 0.
3. *Abel–Jacobi map* (4 sorries): `ofCurve`, `ofCurve_contMDiff`,
   `ofCurve_self`, `ofCurve_inj`. Needs integration-along-paths.
4. *Functoriality + degree* (10 sorries): `pushforward`, `pullback`, their
   `ContMDiff` claims, `*_id_apply` / `*_comp_apply` lemmas, `ContMDiff.degree`,
   and the headline `pushforward_pullback = deg • id`.

**Important finding:** the "functoriality" lemmas (`pushforward_id_apply`,
`pullback_id_apply`, comp variants) cannot be closed by any trivial
placeholder — they constrain `pushforward id = id`, which rules out
e.g. defining `pushforward := 0`.

**Support files (`Jacobians/*.lean`):** 2 stubs remaining —
`instIsManifoldQuotient` and `instLieAddGroupQuotient` in
`ZLatticeQuotient.lean`, both with documented proof sketches. The math
argument is clean (transition maps in the quotient charted space are
locally translations by lattice elements, hence analytic) but the
formalization needs the locally-constant-via-discrete-target lemma that
Mathlib doesn't have in immediate form.

**Build performance (session investment):**
- `Jacobians.lean`: clean build 5 min → 51 s (via `#min_imports`).
- Support files: 7–30 s each with narrow imports.
- Full-project incremental: 9–20 s.

## Aggregated gap ranking (what to build first)

1. **Quotient Lie group instance** on `E ⧸ Λ` for `E` a f.d. normed
   `𝕜`-space and `Λ` an `IsZLattice` — small-to-medium, upstreamable, unblocks
   all `Jacobian X` instances.
2. **Holomorphic 1-forms `Ω¹(X)` on a complex manifold** (at least global
   sections as a ℂ-vector space) — cheap generalization, unblocks
   `Jacobian X` and `pushforward/pullback`.
3. **Path / line integral of a 1-form along a smooth path on a manifold** —
   medium, unblocks `ofCurve` and the period pairing.
4. **Period pairing and proof of `IsZLattice`** — medium on top of 2 and 3;
   needs Riemann bilinear relations.
5. **Topological `genus`** for closed oriented 2-manifolds via `finrank ℤ`
   on `H₁` — small once a usable-enough `H₁` API exists; Hurewicz to bridge
   π₁-abelianization and `H₁` is itself a medium gap.
6. **Mapping degree for proper holomorphic maps** — medium.
7. **`ofCurve_inj` (Abel's theorem)**, **`pushforward_pullback`**, and
   **`genus_eq_zero_iff_homeo`** — each is a headline theorem; the last is
   the hardest (uniformization).

Next session roadmap: start with (1) and (2) as standalone Mathlib-style
contributions.

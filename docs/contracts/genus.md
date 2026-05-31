# Object contract — `genus`

_Prototype object contract (see [`README.md`](README.md) for the format).
Authored 2026-05-31. The machine-checkable cells were verified by
`#print axioms` on this date; regenerate with
[`scripts/axiom_report.lean`](../../scripts/axiom_report.lean)._

```yaml
object: genus
informal: >
  The (geometric) genus of a compact connected Riemann surface X: the
  ℂ-dimension of the space of holomorphic 1-forms on X. Equivalently, the
  number of handles of the underlying real surface. The single most
  important numeric invariant in the challenge — Buzzard's API is built so
  that genus must come out correct (genus_eq_zero_iff_homeo) and so that a
  hack like Jacobian := 0 is blocked by ofCurve_inj in positive genus.
sources:
  - "Forster, Lectures on Riemann Surfaces, §17 (definition via H⁰(X, Ω¹))"
  - "Miranda, Algebraic Curves and Riemann Surfaces, Ch. VI"
  - "Griffiths–Harris, Principles of Algebraic Geometry, Ch. 2 (Hodge)"
lean:
  name: "Jacobians.RiemannSurface.genus"
  signature: >
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] → ℕ
  body: "Module.finrank ℂ (HolomorphicOneForm X)"
characterization:                # the informal "what must be true"
  - id: C1
    claim: "genus(sphere / ℙ¹) = 0"
  - id: C2
    claim: "genus(torus / elliptic curve) = 1"
  - id: C3
    claim: "genus(hyperelliptic y²=f(x), f squarefree, deg f = N) = ⌈N/2⌉ − 1"
  - id: C4   # anti-degeneracy — the property the challenge is designed to force
    claim: "genus ≥ 0 with genus = 0 ⇔ X ≃ sphere; NOT identically 0"
known_values:                    # the test matrix: instance → expected → status
  - instance: ProjectiveLine
    expected: 0
    theorem: Jacobians.ProjectiveCurve.genus_projectiveLine_eq_zero
    status: PROVEN_CORE_AXIOMS                       # ← direct Liouville proof (2026-05-31)
    axiom_deps: []                                   # was [AX_genus_eq_zero_iff_homeo]; retired
  - instance: "Elliptic ω₁ ω₂"
    expected: 1
    theorem: Jacobians.ProjectiveCurve.genus_Elliptic_eq_one
    status: PROVEN_CORE_AXIOMS                       # ← gold cell: no project axioms
    axiom_deps: []
  - instance: HyperellipticEvenProj
    expected: "N/2 − 1"
    theorem: Jacobians.Extensions.HyperellipticEven.genus_HyperellipticEven_eq
    status: proven_mod_axioms__INCLUDING_2_UNSOUND   # see AXIOM_AUDIT.md Class 2d
    axiom_deps:
      - AX_HyperellipticOneForm_eq_form              # Liouville hierarchy L3 (true-but-unproven)
      - AX_HyperellipticAffine_connected
      - hyperellipticEvenCoeff_cocycle_inl_inr_axiom # UNSOUND (false for high deg); task #21
      - hyperellipticEvenCoeff_cocycle_inr_inl_axiom # UNSOUND; task #21
      - affineLiftChart_compat_infinityLiftChart
      - infinityLiftChart_compat_affineLiftChart
      - polynomialLocalHomeomorph_no_critical_in_source   # IFT-shape
      - squareLocalHomeomorph_zero_notMem_source
      - contDiffOn_symm_toOpenPartialHomeomorph
  - instance: HyperellipticOdd
    expected: "(N − 1)/2"
    theorem: "(Extensions/Hyperelliptic.lean — stated)"
    status: sorry
    axiom_deps: []
well_definedness:                # what makes the def non-degenerate at all
  depends_on: instFiniteDimOneForms     # global instance; without it finrank ≡ 0
  source: "derived from Kirov Montel (real ~3,400 LOC), rests on 2 bridge axioms"
anti_degeneracy:
  history: >
    Real bug (caught 2026-04-22): with HolomorphicOneForm = ⊥ and
    FiniteDimensional installed as :=AX over a True∧True carrier, finrank
    collapsed to 0 AND False was derivable via rank_fun_infinite. Fixed:
    carrier is now the real cocycle submodule (holomorphicOneFormSubmodule),
    finite-dim derived from Montel, not asserted.
  current_guard: >
    genus_Elliptic_eq_one = 1 from CORE AXIOMS ONLY positively proves
    HolomorphicOneForm(Elliptic) is genuinely 1-dimensional — i.e. the
    definition is NOT the ⊥-stub on at least one positive-genus curve.
status: validated_on {ProjectiveLine, Elliptic} from core axioms;
        even-hyperelliptic proven mod axioms; odd open.
```

## Reading this card (for a human reviewer)

You can judge `genus` without opening a Lean proof:

1. **Is it the right object?** Read `informal` + `characterization`. The
   definition is `dim_ℂ H⁰(X, Ω¹)`, the standard geometric genus
   (Forster §17). C1–C4 are the textbook facts it must satisfy.

2. **Does it compute correctly where we know the answer?** Read
   `known_values`. Three cells are proven and agree with the classical
   values (0, 1, N/2−1); one (odd) is open. **The status column is the
   honesty surface** — it distinguishes:
   - `PROVEN_CORE_AXIOMS` (Elliptic): fully from Mathlib, nothing
     asserted. This is the strongest possible validation of the
     definition — the machinery genuinely computes genus 1 on a torus.
   - `PROVEN_CORE_AXIOMS` (ProjectiveLine): as of 2026-05-31, `genus ℙ¹ = 0`
     is proved **directly** — `HolomorphicOneForm ProjectiveLine` is a
     subsingleton by a chart-cocycle + Liouville argument
     (`Line/OneForm.lean`), and `finrank` of a subsingleton is 0. The
     uniformization axiom `AX_genus_eq_zero_iff_homeo` is no longer in this
     cell's dependency set. A second fully-validated cell.
   - `proven_mod_axioms__INCLUDING_2_UNSOUND` (even-hyperelliptic): correct
     value, but the named axiom set it reduces to **includes two axioms that
     are false as stated** (`hyperellipticEvenCoeff_cocycle_{inl_inr,inr_inl}_axiom`
     — see `AXIOM_AUDIT.md` Class 2d). So this cell is **not yet a sound
     proof**: the trust boundary is broken until task #21 adds the degree
     bound (the underlying low-degree math is already proven). The Liouville
     L2/L3 deps, by contrast, are true-but-unproven. Read this cell as
     "morally correct at the degrees actually used, but logically resting on
     an inconsistent axiom until task #21."

3. **Could it be the degenerate hack?** Read `anti_degeneracy`. The
   `finrank ≡ 0` collapse was a real bug; it is now positively excluded on
   `Elliptic` (genus 1, gold cell) and on `ProjectiveLine` (where the
   module is provably the *zero* space — the correct non-degenerate answer
   for genus 0 — by direct computation, not the uniformization axiom). It
   is not yet excluded by direct `dim H⁰(Ω¹)` computation on the
   hyperelliptic families (those route through the Liouville axioms);
   that is the remaining definition-validation work.

## What this card says is *not* yet validated

- **C4 anti-degeneracy is asserted, not proven, in general.** The clause
  "genus = 0 ⇔ X ≃ sphere" is `AX_genus_eq_zero_iff_homeo` — an axiom. The
  ⇐ direction (sphere ⇒ genus 0) could in principle be computed; the ⇒
  direction is genuine uniformization. Buzzard's anti-hack lemma
  `ofCurve_inj` (positive genus ⇒ Abel–Jacobi injective) is the companion
  guard and is **also** currently an axiom (`AX_ofCurve_inj`); see the
  sibling experiment discharging it on `Elliptic`.
- **Two known-value cells route through heavy axioms** rather than
  computing `dim H⁰(Ω¹)` directly. They confirm the *value*, not the
  *definition mechanism*, on those curves.

## Highest-value next checks for this object

1. ~~**Direct ℙ¹ computation.**~~ **Done (2026-05-31).** `genus ProjectiveLine
   = 0` is now proved directly: `Subsingleton (HolomorphicOneForm ℙ¹)` via a
   chart-cocycle + Liouville argument in `Line/OneForm.lean`, then `finrank`
   of a subsingleton is 0. The cell is `PROVEN_CORE_AXIOMS`;
   `AX_genus_eq_zero_iff_homeo` retired from it.
2. **Odd-hyperelliptic cell** — mirror the even-side framework (task #21)
   to fill the one `sorry`.
3. Shrink the even-hyperelliptic cell's `axiom_deps`. Liouville **Level 1**
   (`liouville_compact_complex_manifold`) is now **proven** (2026-05-31,
   axiom-free) — the abstract base of the hierarchy. The remaining
   hyperelliptic-specific levels (L2 function-field decomposition, L3 form
   surjectivity) are the project-specific work that still gates this cell.

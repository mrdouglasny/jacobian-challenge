# A1 thinning plan — reduce `AX_torus_uniformization` to a minimal `exp` axiom

**Goal.** Replace the bespoke A1 axiom (`AX_torus_uniformization : TorusSelfAlbanesePresentation m A`
— "the whole self-Albanese presentation exists") with the **single irreducible classical fact**
— existence of the holomorphic group exponential `exp : ℂ^m → A` with `d(exp)₀ = id` — and
**prove the rest** (lattice = `ker exp`, `A ≅ ℂ^m/Λ`, the self-Albanese coordinate identity) as
theorems. Net: same one-axiom dependency for `ofCurve_isJacobian`, but the axiom shrinks from a
large packaged structure to ~4 standard lines, and the nontrivial lattice/quotient/period
deduction becomes machine-checked.

> **Major change** (replaces a soundness-bearing interface axiom). Per `CLAUDE.md`, open a
> GitHub Discussion / tracking issue before the implementing PR; this doc is the proposal.

## Why this and not full discharge
Full axiom-free A1 is blocked on Mathlib *infrastructure*, not on our proof effort: there is **no
Lie-group exponential map, no global manifold flows / complex ODEs, no universal cover** in Mathlib
(a known frontier). Building `exp` from scratch is months-scale foundational diff-geo. The
"divide-by-n chart" shortcut is mathematically invalid at fixed `n` (the chart isn't a local hom;
the group law carries a bilinear error `B(v,w)/n` that only vanishes in the `n→∞` limit — i.e.
rebuilding `exp`). Confirmed by Mathlib survey + Gemini 3.1-pro review (2026-06-14). So we
axiomatize exactly the missing API boundary and prove everything downstream of it.

## The new axiom (minimal `exp` API)
```lean
/-- The holomorphic exponential of a complex torus: a 1-parameter-subgroup chart at the identity.
    The single irreducible classical input (Birkenhake–Lange Ch.1). Satisfiable witness: for the
    concrete torus ℂ^m/Λ, `exp` is the quotient map (holomorphic hom, `d(exp)₀ = id`). -/
structure TorusExp (m : ℕ) (A : Type*) [TopologicalSpace A] [T2Space A] [CompactSpace A]
    [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A] where
  exp        : (Fin m → ℂ) → A
  exp_zero   : exp 0 = 0
  exp_add    : ∀ u v, exp (u + v) = exp u + exp v
  contMDiff  : ContMDiff 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω exp
  mfderiv_zero : mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) exp 0 = ContinuousLinearMap.id ℂ _
                 -- equivalently: `exp` is a local biholomorphism at 0

axiom AX_torus_exp {m : ℕ} {A : Type*} [..instances..] : TorusExp m A
```
**Vetting (do before relying on it):** satisfiable — concrete `ℂ^m/Λ`, `exp = mk`, is a holomorphic
hom with `d(mk)₀ = id`; non-vacuous; correctly typed; strong enough (see deduction below). Send to
Gemini deep-think for (a) typing (b) strength (c) non-vacuity (d) satisfiability, per the axiom
protocol. This *replaces* `AX_torus_uniformization`; vet the swap as a strengthening.

## What becomes a theorem (the ~1–2 week deduction `TorusExp → TorusSelfAlbanesePresentation`)
Build `torus_self_albanese : TorusSelfAlbanesePresentation m A` as a `def` from `AX_torus_exp`:

1. **`ker exp` is discrete.** `mfderiv_zero` ⇒ `exp` is a local homeo at 0 (inverse function theorem,
   `PartialHomeomorph` / `ContMDiffAt` IFT in Mathlib) ⇒ `∃` nbhd `U∋0` with `exp` injective on `U`
   ⇒ `ker exp ∩ U = {0}` ⇒ `DiscreteTopology (ker exp)`.
2. **`exp` surjective.** Local homeo at 0 ⇒ `Set.range exp` is open (it's an open subgroup: `exp_add`
   + open-at-0 by translation) ⇒ clopen ⇒ `A` connected ⇒ `range exp = univ`. *(Identical
   open-subgroup-of-connected argument already used for G4 `curve_generates_jacobian`.)*
3. **`ker exp` is a full `ZLattice`.** discrete (1) + `A ≅ ℂ^m/ker` compact (`A` compact, 2) ⇒ `ker`
   cocompact ⇒ `IsZLattice ℝ (ker exp)` of rank `2m`. Mathlib hooks: `IsZLattice`,
   `IsZLattice.isCompact_range_of_periodic`, `ZLattice.rank`, `instIsZLatticeComap`.
4. **`fromQuot : ℂ^m/Λ → A`** := descend `exp` through `QuotientAddGroup` (it kills `ker`); it's a
   group iso (1-3) and holomorphic (`exp` holo + quotient-manifold charts,
   `Geometry/Manifold/Instances/Quotient.lean`). `liftCoord := Function.surjInv` of `exp` (choice).
   Gives `fromQuot_liftCoord`, `fromQuot_holo`.
5. **Self-Albanese coordinate identity `liftCoord_eq_albanese` (the subtle, meatiest piece).**
   The invariant forms `TorusHolomorphicOneForm m A := Module.Dual ℂ (ℂ^m)` pull back under `exp` to
   the *constant* covectors (translation-invariance + `d(exp)₀ = id`); so for a path `γ : 0 → a`
   lifted to `γ̃` on the cover, `torusLineIntegral ell γ = ∫ ell(γ̃'(t)) dt = ell(γ̃(1) − γ̃(0))`
   (FTC for a linear functional) `= ell(liftCoord a) mod ell(Λ)`. Packaged through
   `torusAlbaneseCoordinateOfFunctional`, this is exactly `liftCoord a − coord(∫_γ) ∈ lattice`
   (the now-sound mod-Λ field). Reuses our `torusLineIntegral` + the discharged
   `AX_torus_oneforms_dualCover` (`TorusHolomorphicOneForm = Module.Dual`, identity dual). Main
   analytic content: `exp`-pullback of an invariant form = constant form, and FTC along the lift.

Then `torus_self_albanese := { (build from AX_torus_exp) with liftCoord_eq_albanese := (5) }`, and
G2/G3/G4 + `ofCurve_isJacobian` are unchanged (they already consume `torus_self_albanese`). Delete
`AX_torus_uniformization`; `ofCurve_isJacobian` `#print axioms` ⇒ std-3 + `AX_torus_exp` + AK.

## Effort / risk
- Steps 1–4: ~1 week (standard, Mathlib ZLattice + IFT + quotient manifolds + the reused G4 argument).
- Step 5: ~1 week (the exp-pullback-of-invariant-form = constant + FTC; our `torusLineIntegral`
  infra helps, but this is genuine analysis — the real effort sink).
- Risk: Mathlib's manifold IFT / `mfderiv`-of-quotient API ergonomics; the FTC-along-lift in step 5.
  None blocked (unlike the full `exp` build) — all pieces exist; this is assembly, not new foundations.

## End state
With this + the AK→0 Kirov port (`ALBANESE_REPOINT_REFACTOR.md`), Albanese categoricity against
**abstract** complex tori rests on exactly **one** minimal classical axiom (`AX_torus_exp`,
"the torus has a holomorphic exp") — everything else (lattice, quotient iso, periods, Jacobi
inversion, self-Albanese identity) proved. Alternative if axiom-free is preferred over abstract-`A`
strength: the concrete-tori escape hatch (carry the presentation as data) → 0 axioms, weaker statement.

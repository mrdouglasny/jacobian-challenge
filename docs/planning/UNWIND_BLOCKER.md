# UNWIND blocker — the non-isolated-point evaluation (2026-06-11)

Status of the lane (`feat/keystone-unwind`, `SerreUnwindDetect.lean`): the §17.7 pole-bound
regularity `GlobalResidue.UnwindRegularity G D` is now a **THEOREM** for the concrete
fine-sheaf residue `G = (cousinResidueData_of_witnessR …).toGlobalResidue`, **conditional on
one residual hypothesis** — the cover-isolation discipline:

```lean
def BadPointsIsolated (𝔇 : ChartDiskCover X) (K D : Divisor X) : Prop :=
  ∀ (E : Divisor X), (∀ x, E x ≤ D x) →
    ∀ f : ↥(linearSystem (X := X) (K - E)),
      (f : MeromorphicFunction X) ∉ linearSystem (X := X) (K - D) →
      ∃ (b : X) (j₀ : 𝔇.toFiniteCover.ι) (n : ℤ),
        MLIsolated 𝔇 j₀ b ∧ (f : MeromorphicFunction X).orderW b = (n : WithTop ℤ) ∧
        E b - K b ≤ n ∧ n < D b - K b

theorem unwindRegularity_concrete_of_isolated
    (hsep : SeparatesPoles 𝔇 K) (hg : IsOneZeroCoeff 𝔇 g) (hexact : SlotExactK 𝔇 g K)
    (hwit : CupMLWitnessR 𝔇 hsep g) (hwitness : ExactOrderWitness 𝔇)
    (hKeff : ∀ x, 0 ≤ K x) (D : Divisor X) (hiso : BadPointsIsolated 𝔇 K D) :
    ((cousinResidueData_of_witnessR hsep g hg (SlotMatchesK_of_exact hexact)
      hwit).toGlobalResidue).UnwindRegularity D
```

(`#print axioms`: standard-3 only.  `ExactOrderWitness` is PROVEN for the canonical chart-disk
cover — `exactOrderWitness_chartDiskCover`; `hKeff` is automatic for the concrete `K = div ω₀`
with `ω₀` holomorphic.)

## The genuine wall — why `BadPointsIsolated` cannot be discharged for all `D`

`exists_bad_point` (proven) always supplies a bad point `b` with finite order in the jump
window `E b − K b ≤ n < D b − K b`; the EXTRA demand is `MLIsolated 𝔇 j₀ b` — `b` lies in
exactly one cover set.  But inside `UnwindRegularity D` the level `E` ranges over ALL divisors
`≤ D`, and bad points live in `supp(D−E)`, which is arbitrary as `E` varies (take
`E = D − 1·x` for any `x`).  A finite cover of a compact connected surface has nonempty
overlaps, so SOME potential bad points are always non-isolated.  No fixed-cover isolation
discipline closes every instance; per-instance discharges (when the specific `v` has its order
violation at an isolated point) do go through with the landed theorem.

## What the unconditional discharge needs

**The multi-chart (non-isolated) evaluation engine.**  All of MLTie / MeroVanish — including
the new marked engine `resFunctional_eq_neg_residue_of_mero_coboundary` — requires the marked
bad point to be `MLIsolated` because the PoU weights are locally constant near the pole
(`eventuallyEq_pouCoeff_one_near_iso`), so the entire smeared residue sits in ONE chart and the
single R0 atom `integral_dbar_smearedSimplePole` evaluates it.  At a non-isolated `b` the PoU
splits the pole across every chart containing `b`; each chart's Stokes term contributes
`−π·ρ_k(b)·r`-style partial weights and only the SUM telescopes to `−π·r` (`∑ρ ≡ 1` near `b`).
Concretely the missing pieces are:

1. **Per-chart smeared-pole atom with non-constant weight**: `∫ ∂̄(χ·(ζ−α)⁻¹) = −π·χ(α)` for a
   compactly-supported smooth `χ` NOT locally constant at `α` (the current R0 atom needs
   `∂̄χ ≡ 0` near `α`; the general statement is Cauchy–Pompeiu for `χ` itself and is TRUE —
   `DbarDisk.cauchyPompeiu_area` is the natural source).
2. **Cross-chart transport of the pole coordinate**: the same point `b` read in two chart
   coordinates; residues transport by the chain rule (`ResidueChangeOfVariables` has the
   simple-pole case `resAt_simplePole_pushforward` — reusable).
3. **The telescoping sum**: `∑_k ρ_k(b) = 1` converts the per-chart contributions into the
   full residue.

Cochain-side the multi-chart matching principal parts are ALREADY available — the skyscraper
`coneB0` construction (`SkyscraperConeRealization`) realizes compatible coefficient cochains on
the whole star of `b` — so the wall is purely the integral evaluation, not the cocycle
construction.

## Alternative routes considered (and why deferred)

* **Cover refinement**: refine the cover so the forced `b` becomes isolated.  Blocked at the
  interface: `UnwindRegularity` is stated on the FIXED cover's `cechH1`, and `G` (its `res`)
  is built on that cover; transporting the detection along a refinement needs the refinement
  homotopy for the residue functional (`CechRefinement*` gives it for classes, not yet for the
  concrete `resFunctional` evaluation).
* **Two-set Forster cover** (his proof uses an ad-hoc two-set cover at `b`): same refinement
  transport problem.

Either route is a full work item; the multi-chart engine (above) is the one that keeps the
established R-lane architecture.

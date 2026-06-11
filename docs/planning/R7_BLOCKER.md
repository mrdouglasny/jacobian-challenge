# R7 blockers — what `Descent.lean` could NOT honestly close (2026-06-10)

`KirovDolbeault/Dolbeault/FineResidue/Descent.lean` lands the germ→coefficient extraction, the
ℂ-linear `resCocycle` on `Z¹(𝒪_K)`, the holomorphic-coboundary vanishing (full
`vanish_coboundary` at `K ≤ 0`), the `liftQ` descent `resH1`, and the conditional assemblies
`cousinResidueData_of_descent` / `cousinResidueData_of_r6`.  Two legs remain genuinely open and
are taken as **named hypotheses** (no sorries, no axioms):

## 1. `hvanish` at general `K` — the K-point-pole coboundary leg

`coboundaries1 K = δ⁰(sections0 K)`.  At `K ≤ 0` every 0-cochain component is an `𝒪`-class and
R5's `resFunctional_eq_zero_of_coboundary` closes the field (PROVEN:
`resCocycle_vanish_coboundary_of_nonpos`).  At genus ≥ 2, `K = div ω₀ > 0` somewhere, and a
`sections0 K` component `h j₀` may carry a **scalar** pole of order ≤ `K a` at a K-point
`a ∈ U j₀` (the form `h·ω₀` is holomorphic — the slot coefficient `g` of `ω₀` vanishes to order
`K a` at `a` — but the scalar is not, so `SmoothOnSets`/`HolomorphicOnSets` fail at `a` and R5's
proof shape does not apply).  Mathematically the integral still vanishes: the contribution at
each K-point is the local residue of the holomorphic form `h·ω₀`, i.e. `0`; in the simple-pole
case this is exactly the R6 tie evaluated at a slot zero (`r · g j₀(α) = r · 0`).  What's
missing formally:

* a **principal-part decomposition** of `sections0 K` cochains at the (cover-isolated) K-points
  (Laurent split into `sections0 0` + finite principal parts), and
* the tie for **higher-order poles** (`K a ≥ 2`): `resFunctional` of the glued cocycle of a
  pole of order `m` against a slot vanishing to order `≥ m` is `0` (Cauchy–Pompeiu /
  bump-cutoff, the same `DbarDisk.cauchyPompeiu_area` mechanism as the in-flight R6, one
  derivative order per pole order).

This is R6b-class analysis (it is the same machinery as `UnwindRegularity`'s residue
evaluation, per the #159 vet).  Recommended order: land R6 (simple-pole tie), then do the
order-`m` generalization once, feeding both this leg and UnwindRegularity.

## 2. `CupMLWitness` — the §17.6 dz/z witness transport through the cup

`nondegenerate_of_r6` PROVES the `nondegenerate` field from `R6Outputs` + `CupMLWitness`.  What
`CupMLWitness` asserts (and what remains): for `0 ≠ v ∈ L(K−D)` there is `ξ ∈ H¹(𝒪_D)` with
`cup v ξ` represented by a cocycle whose extraction agrees on overlaps with an isolated
simple-pole ML cocycle of residue 1, slot-normalized at the pole.  This is Forster §17.6's
`dz/z` construction (the snapshot's `exists_formFnResidue_eq_one_of_localRep_ne_zero` is the
local datum) transported into the port's germ-level cup product (`SerreCupProduct.cup`).
Content: pick a point `a` off the poles/zeros of `v` and of `K−D` with `g j₀(α) ≠ 0`, refine
the cover so `a` is isolated, take `ξ = [the (z−α)⁻¹·v⁻¹-cocycle]`; the cup multiplies by `v`
and leaves the simple pole of residue `g`-normalizable.  Needs: cover refinement at one extra
point + the cup's cocycle-level computation.  Membership conjunct
(`glueCoeff (mlCocycle…) g ∈ oneOneCoeff`) is already proven in the in-flight R6
(`mlGlue_mem_oneOneCoeff`) and becomes redundant once R6 merges.

## 3. Cover-refinement invariance — NOT needed for the assembly (scope note)

`CousinResidueData 𝔘 K` is stated on a fixed cover; the assembly produces it for any
`ChartDiskCover` satisfying `SeparatesPoles 𝔇 K` (which exists by refining the chart-disk cover
at the finitely many K-points — existence not yet formalized; `LerayCoverExists` +
`ChartDiskRefinement` are the natural ingredients).  Refinement *invariance* of the functional
is not required by `SerreResidueRealizationAssembly`'s consumption and was deliberately left
out (the #159 vet's warning about heavy pure-Čech refinement comparison).

## 4. Genus-0 routing (per `docs/planning/R4_G0_NOTE.md`)

At `kirovGenus X = 0` only `g = 0` inhabits `IsOneZeroCoeff`, the fine-sheaf functional is
zero, and `CupMLWitness` is unsatisfiable (no slot value 1) — lane R is conditioned on
`0 < kirovGenus X` and genus 0 goes through the snapshot's `SerreResidueDirectGenus0*` route
(S9).  Do not instantiate the assemblies at genus 0.

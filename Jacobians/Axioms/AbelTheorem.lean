/-
`AX_AbelTheorem`: Abel's theorem on the kernel of the Abel-Jacobi
map on divisors — **now a THEOREM** (flipped 2026-06-12).

**Statement (Lean, refined 2026-04-23; degree-0 restriction added
2026-06-05).** There exists a ℤ-linear
`abelJacobiDiv : Divisor X →+ Jacobian X` extending the Abel-Jacobi
map on points (via `ofCurveImpl`), and on the **degree-zero** divisors
its kernel is exactly the subgroup of principal divisors:

    AddMonoidHom.ker abelJacobiDiv ⊓ AddMonoidHom.ker (Divisor.deg X)
      = PrincipalDivisors X.

The degree-0 restriction is mathematically essential and was missing
before: Abel's theorem is the statement `Div⁰(X) / Principal ≃ Jac(X)`,
and principal divisors are always degree 0 (residue theorem). Without
it the axiom is FALSE — `abelJacobiDiv` sends the basepoint divisor
`(arbitrary)` to `0` (basepoint normalization, `AX_ofCurve_self`), so
that degree-1 divisor sits in the bare kernel but is not principal.
(Caught 2026-06-05 by statement-vetting after `PrincipalDivisors` was
de-opaqued to `range divHom`, which made the bare-kernel form a latent
inconsistency.) All consumers feed only degree-0 divisors (differences
`(Q₁) − (Q₂)`), so the restriction loses nothing.

## Status after the 2026-06-12 split-flip

`AX_AbelTheorem` is now `le_antisymm` over:

* **⊆ (`ker ⊓ ker ≤ Principal`) — PROVEN.**
  `Jacobians.Bridge.abel_subset`: the A-block plumbing
  (`AbelPlumbing.lean`, PR #211) + the unconditional Forster §20
  weak-solution engine (`exists_meromorphic_of_zeroPeriodChain'`,
  E-block, port-side) + the E6 adapter
  (`Jacobians/Bridge/AbelEngineAdapter.lean`). Kernel closure:
  standard 3 + `AX_PeriodCycleBasis` (the Jacobian-layer pin).
* **⊇, degree side (`Principal ≤ ker deg`) — PROVEN.**
  `principalDivisors_le_deg_ker` below, from the degree theorem
  `deg_divisor_eq_zero` (`Cohomology/DegreeTheorem.lean`).
* **⊇, Abel–Jacobi side (`Principal ≤ ker abelJacobiDiv`) — the
  strictly-smaller REMAINDER AXIOM `AX_AbelSupset` below.** Its
  discharge route is the Liouville / symmetric-product argument
  (`docs/planning/ABEL_SUPSET_LIOUVILLE_ROUTE.md`, ~800–1200 LOC,
  no residue theorem / no Stokes).

`abelJacobiDiv` itself moved to `Jacobians/Axioms/AbelJacobiDivDef.lean`
(base-file split) so the proof chain can be imported here without an
import cycle.

## Consequences

* For `g > 0`, `ofCurveImpl X P : X → Jacobian X` is injective. This
  is `AX_ofCurve_inj` — derivable from Abel's full theorem since two
  points give the same Jacobian iff their difference is principal, and
  on a positive-genus curve, a degree-0 principal divisor `P - Q` with
  `P ≠ Q` would contradict the Liouville-like maximum modulus
  principle.
* The image of `abelJacobiDiv` restricted to `Div⁰(X)` (degree-zero
  divisors) is all of `Jacobian X` (Jacobi inversion). Together with
  the kernel statement, this gives `Div⁰(X) / Principal ≃ Jacobian X`
  — the concrete form of the **Jacobian variety as the degree-0
  Picard group** `Pic⁰(X)`.

## History

- 2026-04-23 (A6 in completion plan): promoted from doc-only using the
  `Divisor / PrincipalDivisors / ofCurveImpl` layer.
- 2026-06-12: split-flip. ⊆ proven via the Forster §20 engine + E6
  adapter; ⊇ split into the proven degree half and the remainder
  axiom `AX_AbelSupset`.

See `docs/formalization-plan.md` §7, discharge priority #10;
`docs/completion-plan.md` workstream A6.
Reference: Mumford Vol I §II.3.3–II.3.5; Forster Ch. III (§§20–21).
-/
import Jacobians.Axioms.AbelJacobiDivDef
import Jacobians.RiemannSurface.MeromorphicFunctionField
import Jacobians.RiemannSurface.Cohomology.DegreeTheorem
import Jacobians.RiemannSurface.AbelSupsetLiouville
import Jacobians.Bridge.AbelEngineAdapter

universe u

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- **Abel ⊇, Abel–Jacobi side (former axiom, now a THEOREM — 2026-06-12
SUP-lane flip).** Every principal divisor lies in the kernel of the
Abel-Jacobi map on divisors: for a nonzero global meromorphic function
`f`, `AJ(div f) = 0` in `Jacobian X = ℂ^g/Λ`.

Proof: the Liouville / symmetric-product route, exactly as planned
(`docs/planning/ABEL_SUPSET_LIOUVILLE_ROUTE.md`, rungs S1–S6 of
`docs/planning/SUP_ROUTE.md`): the fiber Abel-Jacobi map
`Φ(y) = AJ(f⁻¹(y))` (`fiberAJ`, S2/S3) is `ContMDiffAt` off the finite
branch locus (local holomorphic sections through the unramified fibers,
S4), continuous everywhere and `MDifferentiable` across the branch
values (cluster decomposition + manifold-valued removable singularity,
S5), and constant by lifting through the lattice covering over the
simply connected `ℙ¹` + Liouville on the compact `ℙ¹` (S6,
`fiberAJConstancy`); then `AJ(div f) = Φ(0) − Φ(∞) = 0`
(`abel_supset_of_fiberAJConstancy`, S3). No residue theorem, no Stokes.

The historical `AX_` name is kept so downstream consumers are untouched
(Phase-C in-place conversion pattern). Kernel closure: standard-3 +
`AX_PeriodCycleBasis` (the Jacobian-layer pin).

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.7
(Abel's theorem, the "only if" direction); Mumford, *Tata Lectures on
Theta* I, §II.3.3–II.3.5; Griffiths–Harris Ch. 2 §2. -/
theorem AX_AbelSupset {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    PrincipalDivisors X ≤ (abelJacobiDiv X).ker :=
  abel_supset_of_fiberAJConstancy (fiberAJConstancy X)

/-- **Principal divisors have degree zero** (subgroup form of the degree
theorem `deg_divisor_eq_zero`): the degree half of Abel ⊇. -/
theorem principalDivisors_le_deg_ker {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    PrincipalDivisors X ≤ (Divisor.deg X).ker := by
  intro D hD
  rw [PrincipalDivisors] at hD
  rcases hD with ⟨f, hdiv⟩
  have hdivisor : MeromorphicFunctionField.divisor f = D := by
    have h := hdiv
    rw [show MeromorphicFunctionField.divHom f =
        Multiplicative.ofAdd (MeromorphicFunctionField.divisor f) from rfl] at h
    exact Multiplicative.ofAdd.injective h
  change Divisor.deg X D = 0
  rw [← hdivisor]
  exact deg_divisor_eq_zero f

/-- **Abel's theorem** (former axiom, now a theorem — 2026-06-12
split-flip). The kernel of the Abel-Jacobi map on degree-zero divisors
is exactly the subgroup of principal divisors. The ⊆ direction is the
Forster §20 weak-solution engine through the E6 adapter
(`Jacobians.Bridge.abel_subset`); the ⊇ direction is the proven degree
theorem plus the remainder axiom `AX_AbelSupset`. The historical `AX_`
name is kept so downstream consumers are untouched (Phase-C in-place
conversion pattern). -/
theorem AX_AbelTheorem {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    (abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker = PrincipalDivisors X :=
  le_antisymm Jacobians.Bridge.abel_subset
    (le_inf AX_AbelSupset principalDivisors_le_deg_ker)

end Jacobians.Axioms

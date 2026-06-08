/-
# Finiteness of Riemann–Roch spaces (`dim L(D) < ∞`) — elementary route

Discharge of the `riemannRochSpace_finiteDimensional` pin (issue #116) via the
elementary upper bound `ℓ(D) ≤ 1 + deg D⁺` (Forster §16 / Miranda Ch. VI), the
"easy half" of Riemann's inequality — Montel-free. See
`docs/planning/riemannRochSpace_finiteDimensional.md`.

Build order: monotonicity → reduce to effective → local coefficient functional
+ kernel → `Multiset` induction → assemble.
-/

import Jacobians.RiemannSurface.Cohomology.RiemannRochSpace

namespace Jacobians.RiemannSurface

open scoped Manifold ContDiff
open Jacobians.Axioms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- **Monotonicity of `L(D)` in the divisor.** If `D ≤ D'` coefficientwise
(`coeff p D ≤ coeff p D'` for all `p`) then `L(D) ⊆ L(D')`: a larger pole
allowance is a weaker constraint. -/
theorem riemannRochSpace_mono {D D' : Divisor X}
    (h : ∀ p, FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)
            ≤ FreeAbelianGroup.coeff p (D' : FreeAbelianGroup X)) :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro F hF p
  have hp := hF p
  refine le_trans ?_ hp
  have hle : (-(FreeAbelianGroup.coeff p (D' : FreeAbelianGroup X)))
            ≤ (-(FreeAbelianGroup.coeff p (D : FreeAbelianGroup X))) :=
    neg_le_neg (h p)
  exact_mod_cast hle

/-- Transport finite-dimensionality **down** a divisor inequality: if `L(D')` is
finite-dimensional and `L(D) ⊆ L(D')`, then `L(D)` is finite-dimensional. The
inclusion `L(D) ↪ L(D')` is injective ℂ-linear, so finiteness pulls back. -/
theorem finiteDimensional_of_riemannRochSpace_le {D D' : Divisor X}
    (h : riemannRochSpace D ≤ riemannRochSpace D')
    [FiniteDimensional ℂ (riemannRochSpace D')] :
    FiniteDimensional ℂ (riemannRochSpace D) :=
  Module.Finite.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

/-! ## The local pole-clearing functional

For a point `p` and `n : ℕ`, twisting a germ's chart pullback by `(z − z0)ⁿ`
(`z0 = chartAt ℂ p p`) clears a pole of order `≤ n` at `p`. The order of the
twist is `n + ord_p(f)`, which is `≥ 0` exactly when `ord_p(f) ≥ -n`. This is
the engine of the one-point induction step. -/

open Topology Filter in
/-- Chart pullback of a germ representative, twisted by `(z − z0)ⁿ`. -/
private noncomputable def localTwist (f : MeroFunctions X) (p : X) (n : ℕ) : ℂ → ℂ :=
  ((· - chartAt ℂ p p) ^ n) * ((f : X → ℂ) ∘ (chartAt ℂ p).symm)

private theorem chartPullback_meromorphicAt (f : MeroFunctions X) (p : X) :
    MeromorphicAt ((f : X → ℂ) ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) := by
  have h := f.property p
  unfold MeromorphicAtX at h
  rwa [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt] at h

private theorem localTwist_meromorphicAt (f : MeroFunctions X) (p : X) (n : ℕ) :
    MeromorphicAt (localTwist f p n) (chartAt ℂ p p) := by
  have hpow : MeromorphicAt ((· - chartAt ℂ p p) ^ n) (chartAt ℂ p p) :=
    (((analyticAt_id (𝕜 := ℂ)).sub analyticAt_const).pow n).meromorphicAt
  exact hpow.mul (chartPullback_meromorphicAt f p)

/-- **Order of the twist** `ord_{z0}((z−z0)ⁿ · f) = n + ord_p(f)`. -/
private theorem localTwist_meromorphicOrderAt (f : MeroFunctions X) (p : X) (n : ℕ) :
    meromorphicOrderAt (localTwist f p n) (chartAt ℂ p p)
      = (n : WithTop ℤ) + orderAt p (f : X → ℂ) := by
  have hpow : MeromorphicAt ((· - chartAt ℂ p p) ^ n) (chartAt ℂ p p) :=
    (((analyticAt_id (𝕜 := ℂ)).sub analyticAt_const).pow n).meromorphicAt
  rw [localTwist, meromorphicOrderAt_mul hpow (chartPullback_meromorphicAt f p),
    meromorphicOrderAt_pow_id_sub_const, orderAt_eq_chartAt]

open Topology Filter in
/-- **The twisted limit exists** when the pole at `p` is order `≤ n`
(`ord_p(f) ≥ -n`): then the twist has order `≥ 0`, so it converges. -/
private theorem localTwist_tendsto_exists (f : MeroFunctions X) (p : X) (n : ℕ)
    (h : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p (f : X → ℂ)) :
    ∃ c, Tendsto (localTwist f p n) (𝓝[≠] (chartAt ℂ p p)) (𝓝 c) := by
  refine tendsto_nhds_of_meromorphicOrderAt_nonneg (localTwist_meromorphicAt f p n) ?_
  rw [localTwist_meromorphicOrderAt]
  -- from `-n ≤ ord` get `0 = (-n) + n ≤ ord + n = n + ord`
  have h2 := add_le_add_left h ((n : ℤ) : WithTop ℤ)
  have hzero : ((-(n : ℤ) : ℤ) : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) = 0 := by
    rw [← WithTop.coe_add]; norm_num
  rw [hzero] at h2
  rw [add_comm]
  simpa using h2

end Jacobians.RiemannSurface

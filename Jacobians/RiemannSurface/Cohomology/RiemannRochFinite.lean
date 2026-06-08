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

section Functional
open Topology Filter

/-- The value of the local pole-clearing functional on a representative: the
punctured-chart limit of the twist (junk `0` if no pole bound, but on `L(D)` the
limit always exists by `localTwist_tendsto_exists`). -/
private noncomputable def localLim (f : MeroFunctions X) (p : X) (n : ℕ) : ℂ :=
  limUnder (𝓝[≠] (chartAt ℂ p p)) (localTwist f p n)

/-- On the order-bounded subspace the twist actually converges to `localLim`. -/
private theorem localTwist_tendsto (f : MeroFunctions X) (p : X) (n : ℕ)
    (h : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p (f : X → ℂ)) :
    Tendsto (localTwist f p n) (𝓝[≠] (chartAt ℂ p p)) (𝓝 (localLim f p n)) := by
  obtain ⟨c, hc⟩ := localTwist_tendsto_exists f p n h
  rwa [localLim, hc.limUnder_eq]

private theorem localTwist_add (f g : MeroFunctions X) (p : X) (n : ℕ) :
    localTwist (f + g) p n = localTwist f p n + localTwist g p n := by
  funext z
  simp only [localTwist, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Function.comp_apply,
    Pi.add_apply, Submodule.coe_add]
  ring

private theorem localTwist_smul (c : ℂ) (f : MeroFunctions X) (p : X) (n : ℕ) :
    localTwist (c • f) p n = c • localTwist f p n := by
  funext z
  simp only [localTwist, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Function.comp_apply,
    Pi.smul_apply, SetLike.val_smul, smul_eq_mul]
  ring

/-- `localLim` is additive on the order-bounded subspace (both limits exist). -/
private theorem localLim_add (f g : MeroFunctions X) (p : X) (n : ℕ)
    (hf : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p (f : X → ℂ))
    (hg : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p (g : X → ℂ)) :
    localLim (f + g) p n = localLim f p n + localLim g p n := by
  have hsum : Tendsto (localTwist (f + g) p n) (𝓝[≠] (chartAt ℂ p p))
      (𝓝 (localLim f p n + localLim g p n)) := by
    rw [localTwist_add]
    exact (localTwist_tendsto f p n hf).add (localTwist_tendsto g p n hg)
  rw [localLim, hsum.limUnder_eq]

/-- `localLim` is homogeneous. -/
private theorem localLim_smul (c : ℂ) (f : MeroFunctions X) (p : X) (n : ℕ)
    (hf : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p (f : X → ℂ)) :
    localLim (c • f) p n = c • localLim f p n := by
  have hs : Tendsto (localTwist (c • f) p n) (𝓝[≠] (chartAt ℂ p p))
      (𝓝 (c • localLim f p n)) := by
    rw [localTwist_smul]
    exact (localTwist_tendsto f p n hf).const_smul c
  rw [localLim, hs.limUnder_eq]

/-- **Well-definedness on the germ quotient:** a germ-zero representative has
`localLim = 0`. -/
private theorem localLim_germZero {g : MeroFunctions X} (hg : g ∈ GermZero X)
    (p : X) (n : ℕ) : localLim g p n = 0 := by
  have htop : meromorphicOrderAt (localTwist g p n) (chartAt ℂ p p) = ⊤ := by
    rw [localTwist_meromorphicOrderAt, hg p]; simp
  have hev : localTwist g p n =ᶠ[𝓝[≠] (chartAt ℂ p p)] 0 :=
    meromorphicOrderAt_eq_top_iff.mp htop
  have htend : Tendsto (localTwist g p n) (𝓝[≠] (chartAt ℂ p p)) (𝓝 0) :=
    Tendsto.congr' hev.symm tendsto_const_nhds
  rw [localLim, htend.limUnder_eq]

/-- **The kernel identity (local form).** For `f` with a pole of order `≤ n` at
`p`, the coefficient `localLim f = 0` exactly when the order is actually `≥ -(n-1)`
— i.e. killing the top Laurent coefficient improves the pole bound by one. -/
private theorem localLim_eq_zero_iff (f : MeroFunctions X) (p : X) (n : ℕ)
    (h : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p (f : X → ℂ)) :
    localLim f p n = 0 ↔ ((-(n : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ orderAt p (f : X → ℂ) := by
  have hzero_iff : localLim f p n = 0 ↔
      Tendsto (localTwist f p n) (𝓝[≠] (chartAt ℂ p p)) (𝓝 0) := by
    constructor
    · intro h0
      have := localTwist_tendsto f p n h
      rwa [h0] at this
    · intro ht
      exact tendsto_nhds_unique (localTwist_tendsto f p n h) ht
  rw [hzero_iff, tendsto_zero_iff_meromorphicOrderAt_pos (localTwist_meromorphicAt f p n),
    localTwist_meromorphicOrderAt]
  -- goal: 0 < ↑n + orderAt p f  ↔  ↑(-↑n + 1) ≤ orderAt p f
  induction (orderAt p (f : X → ℂ)) using WithTop.recTopCoe with
  | top => simp
  | coe k =>
    rw [show (n : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) by norm_cast,
      ← WithTop.coe_add, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) by norm_cast,
      WithTop.coe_lt_coe, WithTop.coe_le_coe]
    omega

/-- **Representative-independence.** Two representatives differing by a germ-zero
function have the same `localLim` (both order-bounded). This descends `localLim`
to the germ quotient `MeroField`. -/
private theorem localLim_congr {f f' : MeroFunctions X} (p : X) (n : ℕ)
    (hd : f - f' ∈ GermZero X)
    (hf' : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p (f' : X → ℂ)) :
    localLim f p n = localLim f' p n := by
  have hbd : ((-(n : ℤ) : ℤ) : WithTop ℤ)
      ≤ orderAt p ((f - f' : MeroFunctions X) : X → ℂ) := by
    rw [hd p]; exact le_top
  have hadd := localLim_add (f - f') f' p n hbd hf'
  rw [sub_add_cancel] at hadd
  rw [hadd, localLim_germZero hd p n, zero_add]

/-! ### Descending the functional to `MeroField` -/

/-- A chosen germ representative of a `MeroField` element. -/
private noncomputable def fieldRep (F : MeroField X) : MeroFunctions X := Quotient.out F

private theorem fieldRep_mk (F : MeroField X) :
    (Submodule.Quotient.mk (fieldRep F) : MeroField X) = F := Quotient.out_eq F

private theorem orderAt_fieldRep (F : MeroField X) (p : X) :
    orderAt p ((fieldRep F : MeroFunctions X) : X → ℂ) = orderAtField p F := by
  conv_rhs => rw [← fieldRep_mk F, orderAtField_mk]

/-- The pole-bound `ord_p F ≥ -n` with `n = (coeff_p D).toNat` holds for **every**
`F ∈ L(D)` (effective or not). -/
private theorem riemannRochSpace_orderBound {D : Divisor X} {F : MeroField X}
    (hF : F ∈ riemannRochSpace D) (p : X) :
    ((-((FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)).toNat : ℤ) : ℤ) : WithTop ℤ)
      ≤ orderAtField p F := by
  refine le_trans ?_ (hF p)
  rw [WithTop.coe_le_coe]
  omega

/-- The local coefficient functional descended to `MeroField` (via the chosen
representative). -/
private noncomputable def localCoeffField (p : X) (n : ℕ) (F : MeroField X) : ℂ :=
  localLim (fieldRep F) p n

private theorem localCoeffField_add {F G : MeroField X} (p : X) (n : ℕ)
    (hF : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAtField p F)
    (hG : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAtField p G) :
    localCoeffField p n (F + G) = localCoeffField p n F + localCoeffField p n G := by
  have hbF : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p ((fieldRep F : MeroFunctions X) : X → ℂ) := by
    rw [orderAt_fieldRep]; exact hF
  have hbG : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p ((fieldRep G : MeroFunctions X) : X → ℂ) := by
    rw [orderAt_fieldRep]; exact hG
  have hdiff : fieldRep (F + G) - (fieldRep F + fieldRep G) ∈ GermZero X := by
    rw [← Submodule.Quotient.eq, fieldRep_mk, Submodule.Quotient.mk_add, fieldRep_mk, fieldRep_mk]
  have hbsum : ((-(n : ℤ) : ℤ) : WithTop ℤ)
      ≤ orderAt p ((fieldRep F + fieldRep G : MeroFunctions X) : X → ℂ) :=
    le_trans (le_min hbF hbG)
      (min_le_orderAt_add ((fieldRep F).property p) ((fieldRep G).property p))
  unfold localCoeffField
  rw [localLim_congr p n hdiff hbsum]
  exact localLim_add (fieldRep F) (fieldRep G) p n hbF hbG

private theorem localCoeffField_smul (c : ℂ) {F : MeroField X} (p : X) (n : ℕ)
    (hF : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAtField p F) :
    localCoeffField p n (c • F) = c • localCoeffField p n F := by
  have hbF : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ orderAt p ((fieldRep F : MeroFunctions X) : X → ℂ) := by
    rw [orderAt_fieldRep]; exact hF
  have hdiff : fieldRep (c • F) - c • fieldRep F ∈ GermZero X := by
    rw [← Submodule.Quotient.eq, fieldRep_mk, Submodule.Quotient.mk_smul, fieldRep_mk]
  have hbsmul : ((-(n : ℤ) : ℤ) : WithTop ℤ)
      ≤ orderAt p ((c • fieldRep F : MeroFunctions X) : X → ℂ) := by
    by_cases hc : c = 0
    · simp [hc]
    · rw [SetLike.val_smul, orderAt_const_smul_of_ne_zero hc p ((fieldRep F : MeroFunctions X) : X → ℂ)]
      exact hbF
  unfold localCoeffField
  rw [localLim_congr p n hdiff hbsmul]
  exact localLim_smul c (fieldRep F) p n hbF

end Functional

end Jacobians.RiemannSurface

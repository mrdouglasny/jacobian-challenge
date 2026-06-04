import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bridge path infrastructure

This file will contain the auxiliary manifold/path construction needed to
replace the structural `bridgePath*` axioms in `KirovLineIntegral.lean`.

The first independent piece is the standard cubic reparameterization
`s ↦ 3s^2 - 2s^3`.  It fixes `0` and `1`, maps `[0, 1]` into `[0, 1]`, and
has zero derivative at both endpoints.  These endpoint-flat facts are the
calculus input for smooth concatenation of chart-local straight segments.
-/

namespace Jacobians.Bridge

/-- The cubic "smoothstep" reparameterization used to flatten segment endpoints. -/
def flatReparam (s : ℝ) : ℝ :=
  3 * s ^ 2 - 2 * s ^ 3

@[simp] theorem flatReparam_zero : flatReparam 0 = 0 := by
  simp [flatReparam]

@[simp] theorem flatReparam_one : flatReparam 1 = 1 := by
  norm_num [flatReparam]

/-- The cubic reparameterization is continuous. -/
theorem continuous_flatReparam : Continuous flatReparam := by
  unfold flatReparam
  fun_prop

/-- The cubic reparameterization is differentiable. -/
theorem differentiable_flatReparam : Differentiable ℝ flatReparam := by
  unfold flatReparam
  fun_prop

/-- The cubic reparameterization is `C^n` for every `n`. -/
theorem contDiff_flatReparam (n : ℕ∞) : ContDiff ℝ n flatReparam := by
  unfold flatReparam
  fun_prop

/-- Derivative of the cubic reparameterization. -/
theorem hasDerivAt_flatReparam (s : ℝ) :
    HasDerivAt flatReparam (6 * s - 6 * s ^ 2) s := by
  unfold flatReparam
  convert (HasDerivAt.sub
    (HasDerivAt.const_mul (3 : ℝ) ((hasDerivAt_id s).pow 2))
    (HasDerivAt.const_mul (2 : ℝ) ((hasDerivAt_id s).pow 3))) using 1
  simp only [id_eq]
  ring_nf

/-- The cubic reparameterization is flat at `0`. -/
theorem hasDerivAt_flatReparam_zero : HasDerivAt flatReparam 0 0 := by
  simpa using hasDerivAt_flatReparam 0

/-- The cubic reparameterization is flat at `1`. -/
theorem hasDerivAt_flatReparam_one : HasDerivAt flatReparam 0 1 := by
  simpa using hasDerivAt_flatReparam 1

/-- Pointwise derivative of the cubic reparameterization. -/
theorem deriv_flatReparam (s : ℝ) :
    deriv flatReparam s = 6 * s - 6 * s ^ 2 :=
  (hasDerivAt_flatReparam s).deriv

@[simp] theorem deriv_flatReparam_zero : deriv flatReparam 0 = 0 := by
  simp [deriv_flatReparam]

@[simp] theorem deriv_flatReparam_one : deriv flatReparam 1 = 0 := by
  norm_num [deriv_flatReparam]

/-- The cubic reparameterization maps the unit interval into itself. -/
theorem flatReparam_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    flatReparam s ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have hs_sq : 0 ≤ s ^ 2 := sq_nonneg s
    have h_factor : 0 ≤ 3 - 2 * s := by nlinarith [hs.2]
    have hprod : 0 ≤ s ^ 2 * (3 - 2 * s) := mul_nonneg hs_sq h_factor
    calc
      0 ≤ s ^ 2 * (3 - 2 * s) := hprod
      _ = flatReparam s := by
        rw [flatReparam]
        ring
  · have hleft_sq : 0 ≤ (1 - s) ^ 2 := sq_nonneg (1 - s)
    have h_factor : 0 ≤ 2 * s + 1 := by nlinarith [hs.1]
    have hprod : 0 ≤ (1 - s) ^ 2 * (2 * s + 1) := mul_nonneg hleft_sq h_factor
    have hdiff : 0 ≤ 1 - flatReparam s := by
      calc
        0 ≤ (1 - s) ^ 2 * (2 * s + 1) := hprod
        _ = 1 - flatReparam s := by
          rw [flatReparam]
          ring
    linarith

/-- The cubic reparameterization sends `[0, 1]` into `[0, 1]`. -/
theorem mapsTo_flatReparam_Icc :
    Set.MapsTo flatReparam (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) :=
  fun _ hs => flatReparam_mem_Icc hs

/-- On `[0, 1]`, the derivative of the cubic reparameterization is nonnegative. -/
theorem deriv_flatReparam_nonneg_of_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ deriv flatReparam s := by
  rw [deriv_flatReparam]
  have hprod : 0 ≤ s * (1 - s) := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
  nlinarith [hprod]

/-- The endpoint-flat cubic reparameterization as a self-map of the unit interval. -/
def flatReparamUnit (s : unitInterval) : unitInterval :=
  ⟨flatReparam s, flatReparam_mem_Icc s.2⟩

@[simp] theorem flatReparamUnit_coe (s : unitInterval) :
    (flatReparamUnit s : ℝ) = flatReparam (s : ℝ) :=
  rfl

@[simp] theorem flatReparamUnit_zero : flatReparamUnit 0 = 0 := by
  apply Subtype.ext
  simp [flatReparamUnit]

@[simp] theorem flatReparamUnit_one : flatReparamUnit 1 = 1 := by
  apply Subtype.ext
  simp [flatReparamUnit]

/-- The unit-interval self-map induced by the cubic reparameterization is continuous. -/
theorem continuous_flatReparamUnit : Continuous flatReparamUnit := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_flatReparam.comp continuous_subtype_val

/-! ## Flat affine segments -/

section FlatSegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine segment from `a` to `b`, reparameterized by `flatReparam`. -/
def flatSegment (a b : E) (t : ℝ) : E :=
  (1 - flatReparam t) • a + flatReparam t • b

@[simp] theorem flatSegment_zero (a b : E) : flatSegment a b 0 = a := by
  simp [flatSegment]

@[simp] theorem flatSegment_one (a b : E) : flatSegment a b 1 = b := by
  simp [flatSegment]

/-- A flat affine segment is continuous. -/
theorem continuous_flatSegment (a b : E) : Continuous (flatSegment a b) := by
  unfold flatSegment
  have hφ : Continuous flatReparam := continuous_flatReparam
  fun_prop

/-- A flat affine segment is differentiable. -/
theorem differentiable_flatSegment (a b : E) : Differentiable ℝ (flatSegment a b) := by
  unfold flatSegment
  have hφ : Differentiable ℝ flatReparam := differentiable_flatReparam
  fun_prop

/-- A flat affine segment is `C^n` for every `n`. -/
theorem contDiff_flatSegment (n : ℕ∞) (a b : E) : ContDiff ℝ n (flatSegment a b) := by
  unfold flatSegment
  have hφ : ContDiff ℝ n flatReparam := contDiff_flatReparam n
  fun_prop

/-- The flat affine segment has zero velocity at its left endpoint. -/
theorem hasDerivAt_flatSegment_zero (a b : E) :
    HasDerivAt (flatSegment a b) (0 : E) 0 := by
  unfold flatSegment
  have hleft : HasDerivAt (fun t : ℝ => 1 - flatReparam t) 0 0 := by
    simpa using
      HasDerivAt.sub (hasDerivAt_const (0 : ℝ) (1 : ℝ)) hasDerivAt_flatReparam_zero
  simpa using
    HasDerivAt.add (hleft.smul_const a) (hasDerivAt_flatReparam_zero.smul_const b)

/-- The flat affine segment has zero velocity at its right endpoint. -/
theorem hasDerivAt_flatSegment_one (a b : E) :
    HasDerivAt (flatSegment a b) (0 : E) 1 := by
  unfold flatSegment
  have hleft : HasDerivAt (fun t : ℝ => 1 - flatReparam t) 0 1 := by
    simpa using
      HasDerivAt.sub (hasDerivAt_const (1 : ℝ) (1 : ℝ)) hasDerivAt_flatReparam_one
  simpa using
    HasDerivAt.add (hleft.smul_const a) (hasDerivAt_flatReparam_one.smul_const b)

end FlatSegment

end Jacobians.Bridge

/-
# The degree theorem `deg(div f) = 0` — shared infrastructure (issue #120)

Toward `deg(div f) = ∑_p ord_p(f) = 0` (degree of a principal divisor is zero),
which gates Serre vanishing (`deg D < 0 ⇒ L(D) = 0`) and feeds `AX_SerreDuality` /
`AX_AbelTheorem`. Build order (`docs/planning/deg_divisor_eq_zero.md`): the shared
bridge first — this file starts with the elementary degree/effective facts.
-/

import Submission.Jacobians.RiemannSurface.Cohomology.RiemannRochSpace
import Submission.Jacobians.RiemannSurface.MeromorphicFunctionField
import Submission.Jacobians.RiemannSurface.DegreeViaP1

universe u v w

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff BigOperators
open Jacobians.Axioms
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.ProjectiveLine
open Jacobians.Vendor.Wallace.HolomorphicForms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder
open MeromorphicFunctionField
open Filter OnePoint


variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- The degree of a divisor is the total of its `Finsupp` coefficients. -/
theorem deg_eq_sum_toFinsupp (D : Divisor X) :
    Divisor.deg X D = (FreeAbelianGroup.toFinsupp D).sum (fun _ n => n) := by
  induction D using FreeAbelianGroup.induction_on with
  | zero => simp
  | of x => simp [Divisor.deg, FreeAbelianGroup.toFinsupp_of, Finsupp.sum_single_index]
  | neg x ih =>
      simp only [map_neg, ih, FreeAbelianGroup.toFinsupp_of]
      rw [show (-(Finsupp.single x (1 : ℤ))) = Finsupp.single x (-1) by
        ext a; simp]
      rw [Finsupp.sum_single_index, Finsupp.sum_single_index] <;> simp
  | add x y hx hy =>
      rw [map_add, hx, hy, map_add, Finsupp.sum_add_index'] <;> simp

/-- **Effective ⇒ degree ≥ 0.** An effective divisor is a sum of nonnegative
coefficients, so its degree is nonnegative. -/
theorem deg_nonneg_of_effective {D : Divisor X} (hD : Effective D) :
    0 ≤ Divisor.deg X D := by
  rw [deg_eq_sum_toFinsupp]
  refine Finset.sum_nonneg (fun x _ => ?_)
  exact hD x

theorem coeff_divisor (f : MeromorphicFunctionField X) (p : X) :
    FreeAbelianGroup.coeff p
      (MeromorphicFunctionField.divisor f : FreeAbelianGroup X) =
      (orderAtMF p f).untop₀ := by
  refine Quotient.inductionOn f ?_
  intro f
  change FreeAbelianGroup.coeff p
      (MeromorphicFunctionField.Rep.divisor f : FreeAbelianGroup X) =
      (orderAt p (f : X → ℂ)).untop₀
  exact MeromorphicFunctionField.Rep.divisor_coeff f p

theorem orderAtMF_ne_top (f : MeromorphicFunctionField X) (p : X) :
    orderAtMF p f ≠ ⊤ := by
  refine Quotient.inductionOn f ?_
  intro f
  simpa [orderAtMF] using f.order_ne_top p

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ) ⊤ X] in
private theorem nontrivial_of_complex_charted : Nontrivial X := by
  classical
  let p : X := Classical.choice (inferInstance : Nonempty X)
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let z₀ : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have htarget_nhds : e.target ∈ 𝓝[≠] z₀ :=
    mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds (e.map_source hp_source))
  haveI : NeBot (𝓝[≠] z₀) := PerfectSpace.not_isolated z₀
  have hboth : e.target ∩ ({z₀}ᶜ : Set ℂ) ∈ 𝓝[≠] z₀ :=
    inter_mem htarget_nhds self_mem_nhdsWithin
  obtain ⟨z, hz_target, hz_ne⟩ := Filter.nonempty_of_mem hboth
  let q : X := e.symm z
  have hq_ne : q ≠ p := by
    intro hqp
    have hz_eq : z = z₀ := by
      have hq_eq : e.symm z = p := by
        simpa [q] using hqp
      calc
        z = e (e.symm z) := (e.right_inv hz_target).symm
        _ = e p := by rw [hq_eq]
        _ = z₀ := rfl
    exact hz_ne hz_eq
  exact ⟨⟨q, p, hq_ne⟩⟩

omit [IsManifold 𝓘(ℂ) ⊤ X] in
private theorem infinite_of_complex_charted : Infinite X := by
  haveI : Nontrivial X := nontrivial_of_complex_charted (X := X)
  exact PreconnectedSpace.infinite

private theorem deg_eq_sum_order_support (f : MeromorphicFunctionField X) :
    Divisor.deg X (MeromorphicFunctionField.divisor f) =
      (orderSupport_finite f).toFinset.sum (fun p => (orderAtMF p f).untop₀) := by
  classical
  rw [deg_eq_sum_toFinsupp]
  let S : Finset X := (orderSupport_finite f).toFinset
  let fs : X →₀ ℤ :=
    FreeAbelianGroup.toFinsupp (MeromorphicFunctionField.divisor f : FreeAbelianGroup X)
  change fs.sum (fun _ n => n) = S.sum (fun p => (orderAtMF p f).untop₀)
  have hsupp : fs.support ⊆ S := by
    intro p hp
    rw [Set.Finite.mem_toFinset]
    have hfs_ne : fs p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hcoeff : fs p = (orderAtMF p f).untop₀ := by
      simpa [fs, FreeAbelianGroup.coeff] using coeff_divisor f p
    have horder_ne : orderAtMF p f ≠ 0 := by
      intro hzero
      apply hfs_ne
      rw [hcoeff, hzero]
      simp
    exact horder_ne
  rw [Finsupp.sum_of_support_subset fs hsupp (fun _ n => n) (by intro p hp; rfl)]
  apply Finset.sum_congr rfl
  intro p hp
  simpa [fs, FreeAbelianGroup.coeff] using coeff_divisor f p

/-- A `toP1`-constant meromorphic-function-field element has vanishing
order everywhere. (De-privatized 2026-06-12: the SUP-lane Abel-⊇ plumbing
needs the constant-function degenerate case `divisor f = 0`.) -/
theorem orderAtMF_eq_zero_of_not_nonconstant {f : MeromorphicFunctionField X}
    (hf : ¬ Nonconstant f) (p : X) :
    orderAtMF p f = 0 := by
  classical
  have hconst : ∃ y₀ : ProjectiveLine, ∀ x : X, toP1 f x = y₀ := by
    by_contra h
    exact hf h
  obtain ⟨y₀, hy₀⟩ := hconst
  haveI : Infinite X := infinite_of_complex_charted (X := X)
  by_cases hyinf : y₀ = (∞ : ProjectiveLine)
  · exfalso
    have hfinite_univ : (Set.univ : Set X).Finite := by
      have hset : {q : X | orderAtMF q f ≠ 0} = Set.univ := by
        ext q
        constructor
        · intro _; trivial
        · intro _
          have hq : toP1 f q = (∞ : ProjectiveLine) := by
            rw [hy₀ q, hyinf]
          exact ((toP1_eq_infty_iff f q).1 hq).ne
      simpa [hset] using orderSupport_finite f
    exact (Set.infinite_univ (α := X)) hfinite_univ
  · obtain ⟨c, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hyinf
    by_cases hc : c = 0
    · exfalso
      subst c
      have hfinite_univ : (Set.univ : Set X).Finite := by
        have hset : {q : X | orderAtMF q f ≠ 0} = Set.univ := by
          ext q
          constructor
          · intro _; trivial
          · intro _
            have hq : toP1 f q = (((0 : ℂ) : ProjectiveLine)) := by
              exact hy₀ q
            exact ((toP1_eq_zero_iff f q).1 hq).ne'
        simpa [hset] using orderSupport_finite f
      exact (Set.infinite_univ (α := X)) hfinite_univ
    · have hnot_neg : ¬ orderAtMF p f < 0 := by
        intro hpole
        have hinfty : toP1 f p = (∞ : ProjectiveLine) :=
          (toP1_eq_infty_iff f p).2 hpole
        rw [hy₀ p] at hinfty
        exact (OnePoint.coe_ne_infty c) hinfty
      have hnot_pos : ¬ 0 < orderAtMF p f := by
        intro hzero
        have hzero_p : toP1 f p = (((0 : ℂ) : ProjectiveLine)) :=
          (toP1_eq_zero_iff f p).2 hzero
        have hc0 : (((0 : ℂ) : ProjectiveLine)) = (c : ProjectiveLine) :=
          hzero_p.symm.trans (hy₀ p)
        have h0c : (0 : ℂ) = c := by
          simpa using hc0
        exact hc h0c.symm
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (orderAtMF_ne_top f p)
      have hn_not_neg : ¬ n < 0 := by
        intro hnneg
        apply hnot_neg
        rw [← hn]
        exact_mod_cast hnneg
      have hn_not_pos : ¬ 0 < n := by
        intro hnpos
        apply hnot_pos
        rw [← hn]
        exact_mod_cast hnpos
      have hn_zero : n = 0 := by omega
      rw [← hn, hn_zero]
      rfl

private theorem deg_divisor_eq_zero_of_not_nonconstant {f : MeromorphicFunctionField X}
    (hf : ¬ Nonconstant f) :
    Divisor.deg X (MeromorphicFunctionField.divisor f) = 0 := by
  rw [deg_eq_sum_order_support f]
  apply Finset.sum_eq_zero
  intro p hp
  simp [orderAtMF_eq_zero_of_not_nonconstant hf p]

private theorem deg_divisor_eq_zero_of_nonconstant {f : MeromorphicFunctionField X}
    (hf : Nonconstant f) :
    Divisor.deg X (MeromorphicFunctionField.divisor f) = 0 := by
  classical
  let S : Finset X := (orderSupport_finite f).toFinset
  let ord : X → ℤ := fun p => (orderAtMF p f).untop₀
  let Spos : Finset X := S.filter (fun p => 0 < orderAtMF p f)
  let Sneg : Finset X := S.filter (fun p => orderAtMF p f < 0)
  have hfilter_not_eq_neg :
      S.filter (fun p => ¬ 0 < orderAtMF p f) = Sneg := by
    apply Finset.filter_congr
    intro p hp
    constructor
    · intro hnot_pos
      have horder_ne : orderAtMF p f ≠ 0 := by
        simpa [S, Set.Finite.mem_toFinset] using hp
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (orderAtMF_ne_top f p)
      have hn_ne : n ≠ 0 := by
        intro hn_zero
        apply horder_ne
        rw [← hn, hn_zero]
        rfl
      have hn_not_pos : ¬ 0 < n := by
        intro hn_pos
        apply hnot_pos
        rw [← hn]
        exact_mod_cast hn_pos
      have hn_neg : n < 0 := by omega
      rw [← hn]
      exact_mod_cast hn_neg
    · intro hneg hpos
      exact (not_lt_of_ge hpos.le) hneg
  have hsplit :
      S.sum ord = Spos.sum ord + Sneg.sum ord := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := S)
      (p := fun p => 0 < orderAtMF p f) (f := ord), hfilter_not_eq_neg]
  have hzero_finset :
      (toP1_zero_fiber_finite f).toFinset = Spos := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      have hp_fiber :
          p ∈ toP1 f ⁻¹' ({(((0 : ℂ) : ProjectiveLine))} : Set ProjectiveLine) := by
        simpa [Set.Finite.mem_toFinset] using hp
      have hpos : 0 < orderAtMF p f := (toP1_eq_zero_iff f p).1 (by simpa using hp_fiber)
      exact Finset.mem_filter.mpr
        ⟨by simpa [S, Set.Finite.mem_toFinset] using hpos.ne', hpos⟩
    · intro hp
      have hpos : 0 < orderAtMF p f := (Finset.mem_filter.mp hp).2
      rw [Set.Finite.mem_toFinset]
      exact (toP1_eq_zero_iff f p).2 hpos
  have hinfty_finset :
      (toP1_infty_fiber_finite f).toFinset = Sneg := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      have hp_fiber :
          p ∈ toP1 f ⁻¹' ({(∞ : ProjectiveLine)} : Set ProjectiveLine) := by
        simpa [Set.Finite.mem_toFinset] using hp
      have hneg : orderAtMF p f < 0 := (toP1_eq_infty_iff f p).1 (by simpa using hp_fiber)
      exact Finset.mem_filter.mpr
        ⟨by simpa [S, Set.Finite.mem_toFinset] using hneg.ne, hneg⟩
    · intro hp
      have hneg : orderAtMF p f < 0 := (Finset.mem_filter.mp hp).2
      rw [Set.Finite.mem_toFinset]
      exact (toP1_eq_infty_iff f p).2 hneg
  let N0 : ℕ := (toP1_zero_fiber_finite f).toFinset.sum (mapAnalyticOrderAt (toP1 f))
  let Ninf : ℕ := (toP1_infty_fiber_finite f).toFinset.sum (mapAnalyticOrderAt (toP1 f))
  have hN_eq : N0 = Ninf := by
    have hzero_fiber_eq :
        (toP1_fiber_finite hf (((0 : ℂ) : ProjectiveLine))).toFinset =
          (toP1_zero_fiber_finite f).toFinset := by
      apply Finset.ext
      intro p
      simp [Set.Finite.mem_toFinset]
    have hinfty_fiber_eq :
        (toP1_fiber_finite hf (∞ : ProjectiveLine)).toFinset =
          (toP1_infty_fiber_finite f).toFinset := by
      apply Finset.ext
      intro p
      simp [Set.Finite.mem_toFinset]
    have hconst := toP1_weightedFiberSum_const (f := f) hf (((0 : ℂ) : ProjectiveLine))
    dsimp [N0, Ninf]
    rwa [hzero_fiber_eq, hinfty_fiber_eq] at hconst
  have hzero_weight_nat :
      N0 = Spos.sum (fun p => Int.toNat (ord p)) := by
    dsimp [N0, ord]
    rw [toP1_zero_weightedFiberSum, hzero_finset]
  have hinfty_weight_nat :
      Ninf = Sneg.sum (fun p => Int.toNat (-(ord p))) := by
    dsimp [Ninf, ord]
    rw [toP1_infty_weightedFiberSum, hinfty_finset]
  have hpos_sum : Spos.sum ord = (N0 : ℤ) := by
    rw [hzero_weight_nat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpos : 0 < orderAtMF p f := (Finset.mem_filter.mp hp).2
    have h_untop_nonneg : 0 ≤ ord p := by
      dsimp [ord]
      have hpos' := hpos
      rw [← WithTop.coe_untop₀_of_ne_top (orderAtMF_ne_top f p)] at hpos'
      exact_mod_cast hpos'.le
    exact (Int.toNat_of_nonneg h_untop_nonneg).symm
  have hneg_sum : Sneg.sum ord = -(Ninf : ℤ) := by
    rw [hinfty_weight_nat, Nat.cast_sum]
    calc
      Sneg.sum ord =
          Sneg.sum (fun p => -(((Int.toNat (-(ord p)) : ℕ) : ℤ))) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hneg : orderAtMF p f < 0 := (Finset.mem_filter.mp hp).2
        have h_untop_neg : ord p < 0 := by
          dsimp [ord]
          have hneg' := hneg
          rw [← WithTop.coe_untop₀_of_ne_top (orderAtMF_ne_top f p)] at hneg'
          exact_mod_cast hneg'
        have hcast : ((Int.toNat (-(ord p)) : ℕ) : ℤ) = -(ord p) := by
          exact Int.toNat_of_nonneg (by omega)
        omega
      _ = -Sneg.sum (fun p => (((Int.toNat (-(ord p)) : ℕ) : ℤ))) := by
        rw [Finset.sum_neg_distrib]
  calc
    Divisor.deg X (MeromorphicFunctionField.divisor f) = S.sum ord := by
      simpa [S, ord] using deg_eq_sum_order_support f
    _ = Spos.sum ord + Sneg.sum ord := hsplit
    _ = (N0 : ℤ) + (-(Ninf : ℤ)) := by rw [hpos_sum, hneg_sum]
    _ = 0 := by
      have hN_eq_int : (N0 : ℤ) = (Ninf : ℤ) := by exact_mod_cast hN_eq
      omega

/-- The degree of the principal divisor of a nonzero global meromorphic function is zero. -/
theorem deg_divisor_eq_zero (f : MeromorphicFunctionField X) :
    Divisor.deg X (MeromorphicFunctionField.divisor f) = 0 := by
  by_cases hf : Nonconstant f
  · exact deg_divisor_eq_zero_of_nonconstant hf
  · exact deg_divisor_eq_zero_of_not_nonconstant hf

/-! ### Bridge to the principal-divisor layer

A *non-zero* `MeroField` element is non-zero **everywhere** (identity principle on
connected `X`), so it has a representative usable as a `MeromorphicFunctionField`
element with a principal divisor. This is the entry point to the bridge. -/

/-- **Identity principle (field form).** A non-zero `F : MeroField X` has finite
order at every point: vanishing on a non-empty open set would force vanishing
everywhere (clopen + connected), contradicting `F ≠ 0`. -/
theorem orderAtField_ne_top_of_ne_zero {F : MeroField X} (hF : F ≠ 0) (p : X) :
    orderAtField p F ≠ ⊤ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (GermZero X) F
  rw [orderAtField_mk]
  have hf_notmem : f ∉ GermZero X := fun hmem =>
    hF ((Submodule.Quotient.mk_eq_zero (GermZero X)).mpr hmem)
  have hex : ∃ q, orderAt q (f : X → ℂ) ≠ ⊤ := by
    by_contra h
    push Not at h
    exact hf_notmem h
  exact orderAt_ne_top_of_exists (fun q => f.property q) hex p

/-- A chosen `MeroFunctions` representative of a `MeroField` element. -/
private noncomputable def rep (F : MeroField X) : MeroFunctions X := Quotient.out F

private theorem rep_mk (F : MeroField X) :
    (Submodule.Quotient.mk (rep F) : MeroField X) = F := Quotient.out_eq F

private theorem orderAt_rep (F : MeroField X) (p : X) :
    orderAt p ((rep F : MeroFunctions X) : X → ℂ) = orderAtField p F := by
  conv_rhs => rw [← rep_mk F, orderAtField_mk]

/-- **The bridge.** A non-zero `MeroField` element as an element of the
principal-divisor layer `MeromorphicFunctionField` (where `div`/`deg` live). -/
noncomputable def toMF {F : MeroField X} (hF : F ≠ 0) : MeromorphicFunctionField X :=
  Quotient.mk Rep.setoid
    { toFun := ((rep F : MeroFunctions X) : X → ℂ)
      meromorphicAt := fun p => (rep F).property p
      order_ne_top := fun p => by
        rw [orderAt_rep]; exact orderAtField_ne_top_of_ne_zero hF p }

/-- The bridge preserves order: `ord_p (toMF F) = ord_p F`. -/
theorem orderAtMF_toMF {F : MeroField X} (hF : F ≠ 0) (p : X) :
    orderAtMF p (toMF hF) = orderAtField p F :=
  orderAt_rep F p

/-- The principal divisor of a non-zero `MeroField` element. -/
noncomputable def divisorOf {F : MeroField X} (hF : F ≠ 0) : Divisor X :=
  MeromorphicFunctionField.divisor (toMF hF)

/-- Its coefficients are the (finite) orders of `F`. -/
theorem coeff_divisorOf {F : MeroField X} (hF : F ≠ 0) (p : X) :
    FreeAbelianGroup.coeff p (divisorOf hF : FreeAbelianGroup X)
      = (orderAtField p F).untop₀ := by
  rw [show (divisorOf hF) = Rep.divisor _ from rfl, Rep.divisor_coeff, orderAt_rep]

/-- **Bridge to membership.** If `F ∈ L(D)` (and `F ≠ 0`) then `div(F) + D` is
effective — exactly the textbook `div f + D ≥ 0` characterizing `L(D)`. -/
theorem effective_divisorOf_add {F : MeroField X} (hF : F ≠ 0) {D : Divisor X}
    (hFD : F ∈ riemannRochSpace D) : Effective (divisorOf hF + D) := by
  intro p
  rw [map_add, coeff_divisorOf]
  have hord := hFD p
  have hfin := orderAtField_ne_top_of_ne_zero hF p
  rw [← WithTop.coe_untop₀_of_ne_top hfin, WithTop.coe_le_coe] at hord
  omega

/-- **Negative-degree vanishing** (modulo the degree theorem). If every principal
divisor has degree zero, then a divisor of negative degree has no global sections:
a non-zero `F ∈ L(D)` would give `0 ≤ deg(div F + D) = deg(div F) + deg D = deg D`,
contradicting `deg D < 0`. This is the Serre-vanishing ingredient. -/
theorem riemannRochSpace_eq_bot_of_deg_neg
    (hdeg0 : ∀ f : MeromorphicFunctionField X,
      Divisor.deg X (MeromorphicFunctionField.divisor f) = 0)
    {D : Divisor X} (hD : Divisor.deg X D < 0) :
    riemannRochSpace D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  by_contra hFne
  have heff := effective_divisorOf_add hFne hF
  have h0 := deg_nonneg_of_effective heff
  have hd0 : Divisor.deg X (divisorOf hFne) = 0 := hdeg0 (toMF hFne)
  rw [map_add, hd0, zero_add] at h0
  omega

/-- **Negative-degree vanishing**, using the degree theorem for principal divisors. -/
theorem riemannRochSpace_eq_bot_of_deg_neg' {D : Divisor X}
    (hD : Divisor.deg X D < 0) :
    riemannRochSpace D = ⊥ :=
  riemannRochSpace_eq_bot_of_deg_neg
    (fun f : MeromorphicFunctionField X => deg_divisor_eq_zero f) hD

end Jacobians.RiemannSurface

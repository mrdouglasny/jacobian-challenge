/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.ResidueAtom
import KirovDolbeault.Dolbeault.FormTraceFibre
import KirovDolbeault.Dolbeault.CanonicalFormDifferential

/-!
# The frame-trace datum for the canonical `ω₀ = df` frame (T lane)

Construction layer for `CanonicalForm17Data.FrameTraceHypothesis` — the LAST residual input of
the keystone (`ResidueAtom.lean`): for the canonical datum with frame `ω₀ = df`, every global
meromorphic `F` admits a `FrameResidueTrace data F`.

## The reduction (proven here): the trace datum from a `LaurentForm` alone

The key structural observation: the `FibreTrace` fields of `FrameResidueTrace` are a
*representation device*, not independent content.  Given the partial-fraction `LaurentForm L`
of the trace, the per-centre fibre datum can be taken to be the **principal-part fibre**
(`principalPartFibre L p`): the single identity sheet over `p` carrying `L.R` itself as its
coefficient.  Its Lemma-3.2 field `hL32` and the finite-centre trace residue are then
*definitional* (`resAt L.R p` on both sides).  Consequently (`frameResidueTrace_of_laurentForm`)
a `FrameResidueTrace data F` exists as soon as a `LaurentForm L` realizes the two honest
geometric identities of Miranda §VIII.3:

* **(fin)** `∑_{p ∈ centres L} Res_p(L.R) = ∑_{y ≠ ∞} ∑_{a ∈ S, F a = y} Res_a(F·ω₀)` — the
  finite-fibre residue transport, and
* **(inf)** `Res_∞(L.R) = ∑_{a ∈ S, F a = ∞} Res_a(F·ω₀)` — the `∞`-fibre residue transport,

over any pole superset `S ⊇ supp(div F) ∪ supp K`.  These two identities are exactly the
content of "`L` represents the trace `Tr_F(F·ω₀)`"; everything else is proven.

## The unramified per-fibre layer (proven here)

Mirroring `FormTraceFibre` with the meromorphic-frame integrand: over a fibre of regular
non-pole points (`FibreRegularData`, frame-free, reused as-is) the `frameFibreTrace` has
per-sheet coefficients the atom's own chart integrands, the per-sheet residue bridge is
`resAt_frameChartIntegrand` (via the proven contour ↔ planar bridge
`resAt_eq_planarCoeff_neg_one`), and Lemma 3.2 over the fibre
(`resAt_traceCoeff_frameFibreTrace`) is unconditional.  For `ω₀ = df` and cover `= f`, the
per-sheet pushforward collapses to the **plain value trace** `F ∘ sheet`
(`frameFibreTrace_traceCoeff_df_eventuallyEq`) — `(f̂ ∘ sheet)' = 1` kills the Jacobian.

## The residual wall (single named `sorry`)

`exists_traceLaurentForm_df` — the §VIII.3 trace assembly for the plain value trace: the
existence of the `LaurentForm` realizing (fin) + (inf) for the `ω₀ = df` datum.  Mathematically
TRUE (Miranda §VIII.3: the value trace of `F` through the branched cover `f` is a rational
function of the base coordinate; its `1`-form `Tr(F)·dw` has finite residues the fibre sums
and `∞`-residue the `∞`-fibre sum).  The proven §5 slit tower constructs exactly this datum
for a holomorphic frame; the `df` instance needs strictly less per-sheet data (the plain value
trace).  Discharge plan: `A_ATOM_ROUTE.md`.

Everything downstream of the wall is proven: `frameTraceHypothesis_of_df` and the existential
`exists_canonicalData_frameTraceHypothesis` feed the keystone corollaries of `ResidueAtom.lean`
(`h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frameTrace`, …).

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), §VIII.3; Forster,
*Lectures on Riemann Surfaces* (GTM 81), §17.3.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Filter

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace Jacobians

namespace Dolbeault

open Jacobians.TraceResidue Jacobians.MeromorphicTrace Jacobians.Dolbeault.FormTraceFibre

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The principal-part fibre: `FrameResidueTrace`'s fibre fields from the `LaurentForm` alone -/

/-- The partial-fraction coefficient `L.R` is meromorphic at every point (finite sum of Laurent
monomials, each meromorphic everywhere). -/
theorem meromorphicAt_laurentR (L : LaurentForm) (p : ℂ) : MeromorphicAt L.R p :=
  MeromorphicAt.fun_sum fun i _ => LaurentForm.meromorphicAt_monomial (L.c i) (L.a i) (L.n i) p

/-- **The principal-part fibre over a centre `p`**: the single identity sheet carrying `L.R`
itself as its coefficient.  Its trace coefficient *is* `L.R`, so the Lemma-3.2 bookkeeping of a
`FrameResidueTrace` built on it is definitional — the honest content moves entirely into the
two aggregate residue identities of the `LaurentForm`. -/
def principalPartFibre (L : LaurentForm) (p : ℂ) : FibreTrace where
  ι := Unit
  fintype_ι := inferInstance
  b := p
  sheet := fun _ => id
  pre := fun _ => p
  sheet_analytic := fun _ => analyticAt_id
  sheet_deriv_ne := fun _ => by simp
  sheet_base := fun _ => rfl
  coeff := fun _ => L.R
  coeff_mero := fun _ => meromorphicAt_laurentR L p

/-- The trace coefficient of the principal-part fibre is `L.R` itself (`deriv id = 1`). -/
theorem principalPartFibre_traceCoeff (L : LaurentForm) (p : ℂ) :
    (principalPartFibre L p).traceCoeff = L.R := by
  funext w
  show ∑ _i : Unit, L.R (id w) * deriv id w = L.R w
  simp

/-! ## The trace datum from a `LaurentForm` realizing the two residue identities -/

/-- **`FrameResidueTrace` from a `LaurentForm` alone (proven reduction).**  Given a
partial-fraction form `L` whose finite residues aggregate to the finite-fibre `frameRes` sums
(**fin**) and whose `∞`-residue is the `∞`-fibre `frameRes` sum (**inf**), the full trace datum
exists: take the principal-part fibres, for which `hL32` and the finite-centre trace residues
are definitional.  This isolates the honest content of the §VIII.3 assembly into the two
hypotheses `hfin`/`hinf`. -/
def frameResidueTrace_of_laurentForm (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (f : MeromorphicFunction X) (S : Finset X)
    (hS : F.div.support ∪ data.K.support ⊆ S) (L : LaurentForm)
    (hfin : ∑ p ∈ Finset.univ.image L.a, resAt L.R p
      = ∑ y ∈ (S.image f.toRiemannSphere).erase OnePoint.infty,
          ∑ a ∈ S with f.toRiemannSphere a = y, frameRes data F a)
    (hinf : resAtInfty L.R L.ρ
      = ∑ a ∈ S with f.toRiemannSphere a = OnePoint.infty, frameRes data F a) :
    FrameResidueTrace data F where
  f := f
  S := S
  hS := hS
  L := L
  fibre := principalPartFibre L
  hL32 := fun p _hp => by
    show ∑ _i : Unit, resAt L.R p = resAt L.R p
    simp
  infty_eq := hinf
  finite_eq := by
    have hcong : ∀ p ∈ Finset.univ.image L.a,
        resAt (principalPartFibre L p).traceCoeff (principalPartFibre L p).b = resAt L.R p :=
      fun p _ => by rw [principalPartFibre_traceCoeff]; rfl
    rw [Finset.sum_congr rfl hcong]
    exact hfin

/-! ## The unramified per-fibre layer for the frame integrand

The mirror of `FormTraceFibre` with the meromorphic-frame chart integrand of the atom itself
(`frameRes`'s integrand) in place of `chartIntegrand ω₀ g`.  The regularity interface
`FibreRegularData` is frame-free and reused as-is (with `g := F.toFun`). -/

/-- **The frame chart integrand** of `α = F·ω₀` at `a`: the integrand of `frameRes data F a`,
named.  `frameRes data F a` is its order-`(−1)` planar coefficient at the chart centre. -/
def frameChartIntegrand (data : CanonicalForm17Data X) (F : MeromorphicFunction X) (a : X) :
    ℂ → ℂ :=
  fun ζ => F.toFun ((chartAt (H := ℂ) a).symm ζ) * formCoeff data.ω₀.toFun a ζ

/-- The frame chart integrand is meromorphic at the chart centre. -/
theorem meromorphicAt_frameChartIntegrand (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (a : X) :
    MeromorphicAt (frameChartIntegrand data F a) ((chartAt (H := ℂ) a) a) :=
  frameRes_integrand_meromorphicAt data F a

/-- **Bridge (c) for the frame integrand**: the contour residue of the frame chart integrand
at the chart centre is `frameRes data F a` — the proven contour ↔ planar bridge
`resAt_eq_planarCoeff_neg_one` applied to the atom's integrand. -/
theorem resAt_frameChartIntegrand (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (a : X) :
    resAt (frameChartIntegrand data F a) ((chartAt (H := ℂ) a) a) = frameRes data F a :=
  resAt_eq_planarCoeff_neg_one (meromorphicAt_frameChartIntegrand data F a)

/-- The chart pullback of `f.holoRepr` at `pre i` evaluates to the base value `b` (frame-free
re-statement of `FibreRegularData.gval`, without the unused holomorphic-frame argument). -/
theorem FormTraceFibre.FibreRegularData.gval' {g : X → ℂ} (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b) (i : D.ι) :
    (fun z => f.holoRepr ((chartAt ℂ (D.xs i)).symm z)) ((chartAt ℂ (D.xs i)) (D.xs i)) = b := by
  show f.holoRepr ((chartAt ℂ (D.xs i)).symm ((chartAt ℂ (D.xs i)) (D.xs i))) = b
  rw [(chartAt ℂ (D.xs i)).left_inv (mem_chart_source ℂ (D.xs i))]
  exact D.hval i

/-- **The frame fibre trace over an unramified fibre**: the `FibreTrace` whose sheets are the
planar section germs of the cover (frame-free, `exists_planar_section`) and whose per-sheet
coefficients are the atom's own frame chart integrands. -/
def frameFibreTrace (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData F.toFun f b) : FibreTrace where
  ι := D.ι
  fintype_ι := D.fintype_ι
  b := b
  sheet := fun i =>
    Classical.choose (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval' f i))
  pre := fun i => (chartAt ℂ (D.xs i)) (D.xs i)
  sheet_analytic := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval' f i))).1
  sheet_deriv_ne := fun i =>
    (Classical.choose_spec
      (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval' f i))).2.2.1
  sheet_base := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval' f i))).2.1
  coeff := fun i => frameChartIntegrand data F (D.xs i)
  coeff_mero := fun i => meromorphicAt_frameChartIntegrand data F (D.xs i)

@[simp] theorem frameFibreTrace_b (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData F.toFun f b) :
    (frameFibreTrace data F f D).b = b := rfl

@[simp] theorem frameFibreTrace_pre (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData F.toFun f b) (i : D.ι) :
    (frameFibreTrace data F f D).pre i = (chartAt ℂ (D.xs i)) (D.xs i) := rfl

@[simp] theorem frameFibreTrace_coeff (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData F.toFun f b) (i : D.ι) :
    (frameFibreTrace data F f D).coeff i = frameChartIntegrand data F (D.xs i) := rfl

/-- **Lemma 3.2 over the unramified fibre, frame form (proven, unconditional)**: the trace
residue of the frame fibre trace at the base equals the fibre sum of the atom's `frameRes`. -/
theorem resAt_traceCoeff_frameFibreTrace (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData F.toFun f b) :
    resAt (frameFibreTrace data F f D).traceCoeff (frameFibreTrace data F f D).b
      = ∑ i, frameRes data F (D.xs i) := by
  rw [(frameFibreTrace data F f D).resAt_traceCoeff']
  exact Finset.sum_congr rfl fun i _ => resAt_frameChartIntegrand data F (D.xs i)

/-- **Per-fibre `frameRes` sum = fibre-restricted pole-set sum** (pure `Finset` re-indexing,
mirror of `fibreResidueSum_eq_filter`): if `xs` injectively enumerates exactly the points of
`S` in the fibre over `coe p`, the per-fibre sum is the filtered sum over `S`. -/
theorem frameFibreResidueSum_eq_filter (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (f : MeromorphicFunction X) {p : ℂ}
    (D : FibreRegularData F.toFun f p) (S : Finset X)
    (hxs_inj : Function.Injective D.xs)
    (hxs_mem : ∀ i, D.xs i ∈ S ∧ f.toRiemannSphere (D.xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ a ∈ S, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) → ∃ i, D.xs i = a) :
    ∑ i, frameRes data F (D.xs i)
      = ∑ a ∈ S with f.toRiemannSphere a = ((p : ℂ) : RiemannSphere), frameRes data F a := by
  classical
  have hImg : (Finset.univ : Finset D.ι).image D.xs
      = S.filter (fun a => f.toRiemannSphere a = ((p : ℂ) : RiemannSphere)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨(hxs_mem i).1, (hxs_mem i).2⟩
    · rintro ⟨ha_mem, ha_fib⟩; exact hxs_surj a ha_mem ha_fib
  rw [← hImg, Finset.sum_image (fun i _ j _ h => hxs_inj h)]

/-! ## The residual wall (single named `sorry`)

The §VIII.3 trace assembly for the canonical `ω₀ = df` frame, reduced (by
`frameResidueTrace_of_laurentForm`) to the existence of the partial-fraction `LaurentForm` of
the trace with its two residue identifications.  Mathematically TRUE: the plain value trace
`Tr(F)(w) = ∑_{sheets over w} F(sheet)` of `F` through the branched cover
`F = f.toRiemannSphere` is a rational function of `w` (Miranda §VIII.3), its `1`-form
`Tr(F)·dw` has at each finite value the fibre residue sum (Lemma 3.2; at a ramification point
of index `e`, the cluster contribution is `planarCoeff_neg_one_branch`'s `e·a_{−e}`), and its
`∞`-residue is the `∞`-fibre sum.  The proven §5 slit tower constructs exactly this datum for
a holomorphic frame (more data than needed here: the `df` per-sheet integrand collapses to the
plain value trace, `frameRes_df_read`). -/

/-- **[THE RESIDUAL WALL — single named `sorry`].**  The partial-fraction `LaurentForm` of the
value trace of `F` through `f`, with the finite-fibre and `∞`-fibre residue transports, for
the canonical `ω₀ = df` datum.  (NOT VERIFIED — Miranda §VIII.3, the trace assembly; see the
module docstring and `A_ATOM_ROUTE.md` for the discharge plan.) -/
theorem exists_traceLaurentForm_df (f : MeromorphicFunction X) (hf : ¬ IsGermConstant f)
    (data : CanonicalForm17Data X) (hω : data.ω₀ = differentialForm f)
    (F : MeromorphicFunction X) :
    ∃ (S : Finset X) (L : LaurentForm),
      F.div.support ∪ data.K.support ⊆ S ∧
      (∑ p ∈ Finset.univ.image L.a, resAt L.R p
        = ∑ y ∈ (S.image f.toRiemannSphere).erase OnePoint.infty,
            ∑ a ∈ S with f.toRiemannSphere a = y, frameRes data F a) ∧
      resAtInfty L.R L.ρ
        = ∑ a ∈ S with f.toRiemannSphere a = OnePoint.infty, frameRes data F a := by
  sorry

/-! ## The trace hypothesis from the wall (proven) -/

/-- **The trace hypothesis for any `ω₀ = df` datum**, conditional on exactly
`exists_traceLaurentForm_df`: every `F` admits a `FrameResidueTrace`, assembled by the proven
reduction `frameResidueTrace_of_laurentForm`. -/
theorem frameTraceHypothesis_of_df (f : MeromorphicFunction X) (hf : ¬ IsGermConstant f)
    (data : CanonicalForm17Data X) (hω : data.ω₀ = differentialForm f) :
    data.FrameTraceHypothesis := by
  intro F
  obtain ⟨S, L, hS, hfin, hinf⟩ := exists_traceLaurentForm_df f hf data hω F
  exact ⟨frameResidueTrace_of_laurentForm data F f S hS L hfin hinf⟩

/-- **The keystone's exact input shape**: a canonical datum with the trace hypothesis exists —
the canonical `ω₀ = df` datum of `exists_nonconstant_meromorphic`, with the hypothesis from
`frameTraceHypothesis_of_df`. -/
theorem exists_canonicalData_frameTraceHypothesis :
    ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis := by
  obtain ⟨_D, f, _hmem, hf⟩ := exists_nonconstant_meromorphic (X := X)
  obtain ⟨K, hK⟩ := exists_differentialForm_divisor f (differentialForm_ne_zero hf)
  exact ⟨canonicalForm17DataOfDivisor f hf K hK,
    frameTraceHypothesis_of_df f hf (canonicalForm17DataOfDivisor f hf K hK) rfl⟩

end Dolbeault

end Jacobians

end

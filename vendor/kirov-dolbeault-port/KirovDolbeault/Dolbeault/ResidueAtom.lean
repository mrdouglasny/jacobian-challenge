/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailFrameGenus0
import KirovDolbeault.Dolbeault.FormResidueTheorem

/-!
# The meromorphic-frame residue atom via the trace datum (A lane)

The discharge skeleton for `CanonicalForm17Data.ResidueAtom` (`TailFrameGenus0.lean`) — the
LAST analytic input of the keystone's genus-0 leg: `∑ₚ Res_p(F·ω₀) = 0` for the canonical
MEROMORPHIC frame `ω₀` (e.g. `ω₀ = df`) and every global meromorphic `F`.

## The route (Route 2 of `G0_BLOCKER.md`, structured like the proven Gate-A shape)

The Gate-A engine (`SerreResidueTheorem.residueTheorem_unconditional`) is parameterized by a
HOLOMORPHIC frame and cannot reach a meromorphic `ω₀` at genus 0
(no factorization `F·ω₀ = α·g` exists there — see `TailFrameGenus0.lean`).  But its
**downstream half** is frame-agnostic: the one-variable sphere-side machinery

* `Jacobians.MeromorphicTrace.FibreTrace` + `resAt_traceCoeff'` (Lemma 3.2, unconditional),
* `Jacobians.MeromorphicTrace.finiteResidueSum_trace_eq_zero_of_fibres'` (the trace combine),
* `resAt_eq_planarCoeff_neg_one` (the contour ↔ planar local-residue bridge),

never sees the frame.  So we mirror `FormResidueTheorem.FormResidueTrace` with the
meromorphic-frame integrand of the atom itself (`frameRes` below): the structure
`FrameResidueTrace data F` packages the §VIII.3 trace assembly output for `F·ω₀` through a
branched cover `f : X → ℙ¹`, and given such a datum for every `F` the atom is a THEOREM
(`CanonicalForm17Data.residueAtom_of_frameTraceHypothesis` — proven below, no sorry).

## Main declarations

* `frameRes data F p` — the atom's per-point planar residue `Res_p(F·ω₀)`, named.
* `frameRes_eq_zero_of_not_mem` — vanishing off `supp(div F) ∪ supp K` (lets the trace datum
  carry any pole superset `S`).
* `frameResSum_eq_fiberwise` / `frameResSum_eq_infty_add_finite` — the fibrewise regrouping
  of `∑ frameRes` along `F = f.toRiemannSphere` (pure `Finset` combinatorics).
* `FrameResidueTrace data F` — the trace datum: a partial-fraction `LaurentForm L`
  representing `Tr_F(F·ω₀)`, per-centre `FibreTrace`s, Lemma-3.2 bookkeeping `hL32`, and the
  `∞`- and finite-fibre residue identifications.
* `frameResSum_eq_zero_of_trace` — **proven**: the datum forces `∑_{p ∈ S} Res_p(F·ω₀) = 0`.
* `CanonicalForm17Data.FrameTraceHypothesis` — **the single residual named input**:
  a `FrameResidueTrace data F` for every `F`.
* `CanonicalForm17Data.residueAtom_of_frameTraceHypothesis` — **the atom from the residual**
  (everything downstream of the trace assembly, proven).
* `exists_residueAtom_of_exists_frameTrace`, `h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frameTrace`
  — the keystone-leg corollaries under the single residual input.
* `planarCoeff_neg_one_branch` — down-payment toward the residual (the X side of the local
  branch-trace identity): at a ramification point of index `e` in normal form, the planar
  residue of `ψ(z)·e·(z−c)^{e−1}` is `e · a_{−e}(ψ)` — pure Laurent shifting.

## Why the residual is honest (satisfiability)

For a HOLOMORPHIC frame, the §5 slit tower *constructs* exactly this datum (that is the
content of `residueTheorem_unconditional` — `FormResidueTheorem.lean` documents the same
trace-representation shape).  For the canonical frame `ω₀ = df` the per-sheet integrand
collapses to the PLAIN value trace of `F` along `f`'s sheets (`(f ∘ sheet)' = 1` kills the
change-of-variables Jacobian), strictly less data than the holomorphic-frame tower needed.
The closure plan is recorded in `A_ATOM_ROUTE.md` / `docs/planning/G0_BLOCKER.md`.

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), §VIII.3 (the trace
`Tr`, Lemma 3.2); Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.3.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Filter

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace Jacobians

namespace Dolbeault

open Jacobians.TraceResidue Jacobians.MeromorphicTrace

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The per-point frame residue -/

/-- **The per-point frame residue** `Res_p(F·ω₀)` of the atom: the order-`(−1)` planar Laurent
coefficient of the chart integrand `(F ∘ chart⁻¹)·formCoeff ω₀` at the chart centre.  This is
verbatim the summand of `CanonicalForm17Data.ResidueAtom`. -/
def frameRes (data : CanonicalForm17Data X) (F : MeromorphicFunction X) (p : X) : ℂ :=
  planarCoeff (-1)
    (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * formCoeff data.ω₀.toFun p ζ)
    ((chartAt (H := ℂ) p) p)

/-- The atom is exactly the vanishing of the `frameRes`-sum over `supp(div F) ∪ supp K`. -/
theorem residueAtom_iff_frameRes (data : CanonicalForm17Data X) :
    data.ResidueAtom ↔ ∀ F : MeromorphicFunction X,
      ∑ p ∈ F.div.support ∪ data.K.support, frameRes data F p = 0 :=
  Iff.rfl

/-- The frame integrand is meromorphic at the chart centre (product of the two chart reads). -/
theorem frameRes_integrand_meromorphicAt (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (p : X) :
    MeromorphicAt
      (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * formCoeff data.ω₀.toFun p ζ)
      ((chartAt (H := ℂ) p) p) :=
  (F.meromorphic p).mul (data.ω₀.meromorphic p)

/-- **Off-support vanishing**: away from `supp(div F) ∪ supp K` both chart reads have
nonnegative order, so the product's order is `≥ 0 > −1` and the planar residue vanishes.
This is what lets the trace datum carry an arbitrary finite pole superset `S`. -/
theorem frameRes_eq_zero_of_not_mem (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) {p : X}
    (hp : p ∉ F.div.support ∪ data.K.support) : frameRes data F p = 0 := by
  rw [Finset.mem_union] at hp
  push Not at hp
  obtain ⟨hpF, hpK⟩ := hp
  -- the `F` read has nonnegative order
  have hFord : (0 : WithTop ℤ) ≤
      meromorphicOrderAt (F.toFun ∘ (chartAt (H := ℂ) p).symm) ((chartAt (H := ℂ) p) p) := by
    have h0 : F.orderAtPoint p = 0 := Finsupp.notMem_support_iff.mp hpF
    rw [MeromorphicFunction.orderAtPoint] at h0
    rcases eq_or_ne (meromorphicOrderAt (F.toFun ∘ (chartAt (H := ℂ) p).symm)
        ((chartAt (H := ℂ) p) p)) ⊤ with htop | hne
    · rw [htop]; exact le_top
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hn]
      rw [← hn, WithTop.untop₀_coe] at h0
      exact_mod_cast le_of_eq h0.symm
  -- the frame read has order `K p = 0`
  have hKord : meromorphicOrderAt (formCoeff data.ω₀.toFun p) ((chartAt (H := ℂ) p) p)
      = (0 : WithTop ℤ) := by
    have hK0 : data.K p = 0 := Finsupp.notMem_support_iff.mp hpK
    have h := data.order_eq p
    rw [MeromorphicOneForm.formOrderW] at h
    rw [h, hK0]
    norm_num
  -- product order `≥ 0 > −1` kills the planar residue
  have hord : ((-1 : ℤ) : WithTop ℤ) <
      meromorphicOrderAt
        (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * formCoeff data.ω₀.toFun p ζ)
        ((chartAt (H := ℂ) p) p) := by
    have hmul := meromorphicOrderAt_mul (F.meromorphic p) (data.ω₀.meromorphic p)
    have hprod_eq : (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ)
        * formCoeff data.ω₀.toFun p ζ)
        = (F.toFun ∘ (chartAt (H := ℂ) p).symm) * formCoeff data.ω₀.toFun p := rfl
    rw [hprod_eq, hmul]
    have h0le : (0 : WithTop ℤ) ≤ meromorphicOrderAt (F.toFun ∘ (chartAt (H := ℂ) p).symm)
        ((chartAt (H := ℂ) p) p) + meromorphicOrderAt (formCoeff data.ω₀.toFun p)
        ((chartAt (H := ℂ) p) p) := by
      rw [hKord, add_zero]
      exact hFord
    refine lt_of_lt_of_le ?_ h0le
    exact_mod_cast (by norm_num : (-1 : ℤ) < 0)
  exact planarCoeff_eq_zero_of_lt_order hord (frameRes_integrand_meromorphicAt data F p)

/-! ## The fibrewise regrouping along the cover

Identical combinatorics to `FormResidueTheorem.residueSum_eq_fiberwise` /
`residueSum_eq_infty_add_finite`, with `frameRes data F` in place of `formFnResidue ω₀ g`. -/

/-- **Fibrewise regrouping**: the `frameRes`-sum over `S` partitions along the fibres of
`F = f.toRiemannSphere`. -/
theorem frameResSum_eq_fiberwise (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) (S : Finset X) :
    ∑ p ∈ S, frameRes data F p
      = ∑ y ∈ S.image f.toRiemannSphere,
          ∑ p ∈ S with f.toRiemannSphere p = y, frameRes data F p :=
  (Finset.sum_fiberwise_of_maps_to (fun _ hx => Finset.mem_image_of_mem _ hx) _).symm

/-- The fibrewise regrouping, split into the `∞`-fibre and the finite-value fibres. -/
theorem frameResSum_eq_infty_add_finite (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (f : MeromorphicFunction X) (S : Finset X) :
    ∑ p ∈ S, frameRes data F p
      = (∑ p ∈ S with f.toRiemannSphere p = OnePoint.infty, frameRes data F p)
        + ∑ y ∈ (S.image f.toRiemannSphere).erase OnePoint.infty,
            ∑ p ∈ S with f.toRiemannSphere p = y, frameRes data F p := by
  classical
  rw [frameResSum_eq_fiberwise]
  by_cases hmem : OnePoint.infty ∈ S.image f.toRiemannSphere
  · rw [← Finset.add_sum_erase _ _ hmem]
  · rw [Finset.erase_eq_of_notMem hmem]
    have hempty : (S.filter (fun p => f.toRiemannSphere p = OnePoint.infty)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hpS hcontra
      exact hmem (hcontra ▸ Finset.mem_image_of_mem _ hpS)
    rw [hempty, Finset.sum_empty, zero_add]

/-! ## The trace datum

The meromorphic-frame mirror of `FormResidueTheorem.FormResidueTrace`: the §VIII.3 output for
`α = F·ω₀` through a branched cover `f`.  Each field is a TRUE statement of the trace
assembly (Miranda §VIII.3); for a holomorphic frame the proven §5 slit tower constructs it
(see `FormResidueTheorem.lean`), so the structure is non-vacuous and not a disguised `False`. -/

/-- **The meromorphic-frame trace datum** of `α = F·ω₀` through `F = f.toRiemannSphere`:

* `f` — a meromorphic function giving the branched cover;
* `S` — a finite pole superset, `⊇ supp(div F) ∪ supp K` (off the union the residue already
  vanishes, `frameRes_eq_zero_of_not_mem`);
* `L` — the partial-fraction `LaurentForm` on `ℂℙ¹` representing `Tr_F(F·ω₀)`;
* `fibre p` — the per-centre fibre datum (sheets, sections, per-sheet coefficients);
* `hL32` — Lemma 3.2's bookkeeping at the finite centres: the fibre-residue sum equals `L`'s
  residue there;
* `infty_eq` / `finite_eq` — the `∞`-fibre and finite-fibre identifications of the trace
  residues with the manifold-side `frameRes` sums. -/
structure FrameResidueTrace (data : CanonicalForm17Data X) (F : MeromorphicFunction X) where
  /-- The meromorphic function giving the branched cover `F = f.toRiemannSphere`. -/
  f : MeromorphicFunction X
  /-- The finite pole superset of `α = F·ω₀`. -/
  S : Finset X
  /-- `S` contains the atom's support `supp(div F) ∪ supp K`. -/
  hS : F.div.support ∪ data.K.support ⊆ S
  /-- The partial-fraction `1`-form on `ℂℙ¹` representing `Tr_F(F·ω₀)`. -/
  L : LaurentForm
  /-- The fibre datum over each finite centre. -/
  fibre : ℂ → FibreTrace
  /-- Lemma 3.2 at each finite centre: the fibre-residue sum equals `L`'s residue. -/
  hL32 : ∀ p ∈ (Finset.univ.image L.a),
    (∑ i, resAt ((fibre p).coeff i) ((fibre p).pre i)) = resAt L.R p
  /-- The `∞`-residue of the trace is the `∞`-fibre residue sum. -/
  infty_eq : resAtInfty L.R L.ρ
    = ∑ p ∈ S with f.toRiemannSphere p = OnePoint.infty, frameRes data F p
  /-- The finite-centre trace-residue total is the finite-fibre residue sum. -/
  finite_eq : (∑ p ∈ Finset.univ.image L.a, resAt (fibre p).traceCoeff (fibre p).b)
    = ∑ y ∈ (S.image f.toRiemannSphere).erase OnePoint.infty,
        ∑ p ∈ S with f.toRiemannSphere p = y, frameRes data F p

/-- **The frame residue theorem from the trace datum** (proven, frame-agnostic downstream):
given a `FrameResidueTrace data F`, the total frame residue over its pole set vanishes.
Verbatim the `residueSum_eq_zero_of_formResidueTrace` argument: the unconditional sphere-side
combine + the two identifications + the fibrewise regrouping. -/
theorem frameResSum_eq_zero_of_trace (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (T : FrameResidueTrace data F) :
    ∑ p ∈ T.S, frameRes data F p = 0 := by
  have hcombine := finiteResidueSum_trace_eq_zero_of_fibres' T.L T.fibre T.hL32
  rw [T.finite_eq, T.infty_eq] at hcombine
  rw [frameResSum_eq_infty_add_finite data F T.f T.S, add_comm]
  exact hcombine

/-! ## The single residual named input, and the atom from it -/

/-- **[THE SINGLE RESIDUAL NAMED INPUT of the A lane].**  The §VIII.3 trace assembly for the
meromorphic frame: every global meromorphic `F` admits a `FrameResidueTrace data F`.
Mathematically TRUE on every compact Riemann surface (it is what the §5 slit tower constructs
for a holomorphic frame; for `ω₀ = df` the per-sheet integrand is the plain value trace).
Discharge plan: `A_ATOM_ROUTE.md` / `docs/planning/G0_BLOCKER.md`. -/
def CanonicalForm17Data.FrameTraceHypothesis (data : CanonicalForm17Data X) : Prop :=
  ∀ F : MeromorphicFunction X, Nonempty (FrameResidueTrace data F)

/-- **The residue atom from the trace hypothesis** (everything downstream of the trace
assembly, proven): extend the atom's support sum to the datum's pole superset by
`frameRes_eq_zero_of_not_mem`, then apply the trace-datum residue theorem. -/
theorem CanonicalForm17Data.residueAtom_of_frameTraceHypothesis
    (data : CanonicalForm17Data X) (h : data.FrameTraceHypothesis) :
    data.ResidueAtom := by
  rw [residueAtom_iff_frameRes]
  intro F
  obtain ⟨T⟩ := h F
  have hext : ∑ p ∈ F.div.support ∪ data.K.support, frameRes data F p
      = ∑ p ∈ T.S, frameRes data F p := by
    refine Finset.sum_subset T.hS fun p _ hpnot => ?_
    exact frameRes_eq_zero_of_not_mem data F hpnot
  rw [hext]
  exact frameResSum_eq_zero_of_trace data F T

/-! ## The keystone-leg corollaries under the residual input -/

/-- Atom existence from trace-hypothesis existence (the genus-0 leg's exact input shape). -/
theorem exists_residueAtom_of_exists_frameTrace
    (h : ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis) :
    ∃ data : CanonicalForm17Data X, data.ResidueAtom := by
  obtain ⟨data, hdata⟩ := h
  exact ⟨data, data.residueAtom_of_frameTraceHypothesis hdata⟩

/-- **The canonical-cover genus identity under the trace hypothesis**: `h¹(𝒪) = kirovGenus`
at the canonical chart-disk cover, with the trace assembly needed in the `g = 0` case only
(`kirovGenus X > 0` is covered by the holomorphic-form witness). -/
theorem h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frameTrace
    (h0 : kirovGenus X = 0 → ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis) :
    (chartDiskCover (X := X)).toFiniteCover.h1Dim (0 : Divisor X) = kirovGenus X :=
  h1Dim_zero_chartDiskCover_eq_kirovGenus_of_genus_split
    (fun hg => exists_residueAtom_of_exists_frameTrace (h0 hg))

/-- **The keystone `g = 0` leg under the trace hypothesis**: `Nonempty (SerreDualityData 𝔘)`
at `kirovGenus X = 0` from the trace assembly alone. -/
theorem exists_serreDualityData_of_genus_zero_of_frameTrace (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable)
    (h : ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis)
    (hg0 : kirovGenus X = 0) :
    Nonempty (SerreDualityData 𝔘) := by
  obtain ⟨data, hdata⟩ := h
  exact exists_serreDualityData_of_genus_zero_of_residueAtom 𝔘 hR data
    (data.residueAtom_of_frameTraceHypothesis hdata) hg0

/-! ## Down-payment toward the residual: the local branch-trace normalization (X side)

At a ramification point of index `e` of the cover (normal form `w = w₀ + z^e` in centred
coordinates), the canonical frame reads `df = e·(z−c)^{e−1} dz` (times a unit absorbed into
`ψ`), so the per-point residue of `F·df` is the `(−e)`-th Laurent coefficient of the sheet
integrand, weighted by `e`.  This is the X-side half of the local branch-trace identity
`∑_{fibre} Res = Res(trace)` (the sphere side is the trace's `a_{−1}` read, supplied by the
trace datum); pure Laurent shifting, no contours. -/

/-- **The branch normalization**: `Res_c(ψ(z)·e·(z−c)^{e−1} dz) = e·a_{−e}(ψ)` — the planar
residue of the index-`e` normal-form integrand is `e` times the depth-`e` planar coefficient. -/
theorem planarCoeff_neg_one_branch {ψ : ℂ → ℂ} {c : ℂ} (hψ : MeromorphicAt ψ c) (e : ℕ) :
    planarCoeff (-1) (fun z => ψ z * ((e : ℂ) * (z - c) ^ ((e : ℤ) - 1))) c
      = (e : ℂ) * planarCoeff (-(e : ℤ)) ψ c := by
  have hswap : (fun z => ψ z * ((e : ℂ) * (z - c) ^ ((e : ℤ) - 1)))
      = (e : ℂ) • (fun z => (z - c) ^ ((e : ℤ) - 1) * ψ z) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hmono : MeromorphicAt (fun z => (z - c) ^ ((e : ℤ) - 1) * ψ z) c :=
    (meromorphicAt_zpow_self c ((e : ℤ) - 1)).mul hψ
  rw [hswap, planarCoeff_smul (e : ℂ) hmono, planarCoeff_monomial_mul ((e : ℤ) - 1) (-1) hψ]
  congr 2
  ring

end Dolbeault

end Jacobians

end

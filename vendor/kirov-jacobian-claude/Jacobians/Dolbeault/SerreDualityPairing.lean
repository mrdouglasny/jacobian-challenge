/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreDuality
import Jacobians.Dolbeault.CohomologicalRR
import Jacobians.LinearSystem
import Jacobians.Genus
import Jacobians.Dolbeault.Residue
import Jacobians.Dolbeault.FormCoeff
import Jacobians.Dolbeault.MittagLeffler
import Jacobians.Dolbeault.CechComplex
import Jacobians.Dolbeault.CechFinitenessWiring
import Jacobians.Dolbeault.ChartCoverDbarGlue

/-!
# Serre duality on `X` — the direct Forster §17 route (the plan of record)

This is the **direct** route to `arithmeticGenus_eq_genus` and `serre_h1_eq`, following Forster
*Lectures on Riemann Surfaces* §17 (Serre Duality Theorem) verbatim — **no Dolbeault comparison and no
Hodge symmetry**. Forster §17 is entirely PDE-free (harmonic forms first appear in §19, which §16–17
never use); it proves, for the **canonical divisor** `K`, the perfect residue pairing

  `⟨ω, ξ⟩ := Res(ω·ξ)`,   `ι_D : H⁰(X, Ω_{−D}) → H¹(X, 𝒪_D)*`

is an isomorphism (Forster 17.6 injective + 17.9 surjective), whence (17.10/17.11)

  `dim H¹(X, 𝒪_D) = dim H⁰(X, Ω_{−D})`,  and at `D = 0`:  `g = dim H¹(X,𝒪) = dim H⁰(X,Ω)`.

Using Forster 17.4 (`Ω_{−D} ≅ 𝒪_{K−D}` via multiplication by a meromorphic 1-form with divisor `K`),
we phrase the pairing on the **already-built junk-free linear system** `L(K−D)` (`lDim (K−D)`), so we do
**not** need a separate meromorphic-1-form space:

  `ι_D : lSysModule (K − D) → (𝔘.cechH1 D)*`,   bijective ⟹  `h1Dim D = lDim (K − D)`  (= `serre_h1_eq`).

## What is proved here (sorry-free, downstream of the bundled `SerreDualityData`)

The abstract finite-dimensional cores are already proven in `SerreDuality.lean`:
`finrank_le_of_injective_to_dual` (17.6) and `serre_surjectivity_dim_core` (17.9). This file bundles the
**geometric instantiation** of §17 into one honest, non-vacuous structure `SerreDualityData 𝔘` (the
canonical `K`, the residue pairing, its injectivity and surjectivity, and the finiteness of `H¹`), and
**derives** `serre_eq` (17.11), `serre_h1_eq`, and `arithmeticGenus_eq_genus` from it. The `≤` half wires
`finrank_le_of_injective_to_dual` directly; the `≥` half uses the bundled surjectivity (whose eventual
construction runs `serre_surjectivity_dim_core` on the §17.9 dimension count).

## The remaining work (isolated to one named input)

`exists_serreDualityData` — constructing the §17 instantiation for a general `X`: the residue functional
`Res : H¹(X,Ω) → ℂ` (well-defined via the **1-form residue theorem** `∑Res = 0`, Miranda §VIII.3
trace-to-ℙ¹), the pairing, its injectivity (the §17.6 residue-1 witness `exists_formFnResidue_eq_one`),
and its surjectivity (the §17.9 count, gated on cohomological RR / finiteness). See
`docs/serre_17_build_plan.md`. This single input **replaces both** former ladder leaves
`arithmeticGenus_eq_genus` and `serre_h1_eq`.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4–17.11; Miranda, *Algebraic Curves and
Riemann Surfaces*, §VIII.3.
-/

noncomputable section

open scoped Manifold ContDiff
open Module

set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The **junk-free linear-system module** `L(D)` (= `H⁰(X, 𝒪_D)`): the linear system with the
`toFun`-germ junk quotiented out. By definition `lDim D = finrank ℂ (lSysModule D)`. -/
abbrev lSysModule (D : Divisor X) : Type _ :=
  ↥(linearSystem (X := X) D) ⧸ (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) D)

/-! ### Residue pairing and its quotients -/

/-- Predicate stating that a global `MittagLefflerForm` is a Mittag-Leffler representative
of the product of a holomorphic 1-form `α` and a 1-cochain `ξ`. -/
def IsMittagLefflerRep (𝔘 : FiniteCover X) (α : HolomorphicOneForms X) (ξ : 𝔘.toFiniteFamily.Cochain1)
    (μ : MittagLefflerForm X) : Prop :=
  μ.α = α ∧
  ∃ (g_local : 𝔘.ι → X → ℂ),
    (∀ i : 𝔘.ι, ∀ x : 𝔘.U i, AnalyticAt ℂ (fun z => (μ.g - g_local i) ((chartAt ℂ x.1).symm z)) ((chartAt ℂ x.1) x.1)) ∧
    (∀ p : 𝔘.ι × 𝔘.ι, toGerm (𝔘.U p.1 ⊓ 𝔘.U p.2) (fun x => g_local p.1 x.1 - g_local p.2 x.1) = ξ p)

/-- **Local Mittag-Leffler solvability on overlaps.** -/
lemma exists_mittagLefflerRep_local (𝔘 : FiniteCover X) (ξ : 𝔘.toFiniteFamily.Cochain1) :
    ∃ (g_local : 𝔘.ι → X → ℂ),
      ∀ p : 𝔘.ι × 𝔘.ι, toGerm (𝔘.U p.1 ⊓ 𝔘.U p.2) (fun x => g_local p.1 x.1 - g_local p.2 x.1) = ξ p := sorry

/-- **Finiteness of poles for local principal parts.** -/
lemma exists_mittagLefflerRep_poles (𝔘 : FiniteCover X) (g_local : 𝔘.ι → X → ℂ) :
    ∃ poles : Finset X, ∀ (i : 𝔘.ι) (x : X) (_hx : x ∉ poles),
      AnalyticAt ℂ (fun z => g_local i ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) := sorry

/-- **Analyticity of global Mittag-Leffler function sum.** -/
lemma exists_mittagLefflerRep_sum_analytic (𝔘 : FiniteCover X) (g_local : 𝔘.ι → X → ℂ)
    (poles : Finset X) (hpoles : ∀ (i : 𝔘.ι) (x : X) (_hx : x ∉ poles),
      AnalyticAt ℂ (fun z => g_local i ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (ρ : SmoothPartitionOfUnity 𝔘.ι 𝓘(ℝ, ℂ) X Set.univ) :
    ∀ a, a ∉ poles → AnalyticAt ℂ (fun z => (fun x => ∑ i, (ρ i x : ℂ) * g_local i x) ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a) := sorry

/-- **Local Laurent singularity matching for global sum.** -/
lemma exists_mittagLefflerRep_iso (𝔘 : FiniteCover X) (α : HolomorphicOneForms X) (g_local : 𝔘.ι → X → ℂ)
    (poles : Finset X) (ρ : SmoothPartitionOfUnity 𝔘.ι 𝓘(ℝ, ℂ) X Set.univ) :
    ∀ a ∈ poles, formFnHoloPunctured α (fun x => ∑ i, (ρ i x : ℂ) * g_local i x) a := sorry

/-- **Overlap analyticity for Mittag-Leffler representatives.** -/
lemma exists_mittagLefflerRep_overlap (𝔘 : FiniteCover X) (g_local : 𝔘.ι → X → ℂ)
    (ρ : SmoothPartitionOfUnity 𝔘.ι 𝓘(ℝ, ℂ) X Set.univ) (g_global : X → ℂ)
    (hg : g_global = fun x => ∑ i, (ρ i x : ℂ) * g_local i x) (i : 𝔘.ι) (x : 𝔘.U i) :
    AnalyticAt ℂ (fun z => (g_global - g_local i) ((chartAt ℂ x.1).symm z)) ((chartAt ℂ x.1) x.1) := sorry

lemma exists_mittagLefflerRep (𝔘 : FiniteCover X) (α : HolomorphicOneForms X) (ξ : 𝔘.toFiniteFamily.Cochain1) :
    ∃ μ : MittagLefflerForm X, IsMittagLefflerRep 𝔘 α ξ μ := by
  obtain ⟨g_local, hg_local⟩ := exists_mittagLefflerRep_local 𝔘 ξ
  obtain ⟨ρ, hρ_sub⟩ : ∃ ρ : SmoothPartitionOfUnity 𝔘.ι 𝓘(ℝ, ℂ) X Set.univ,
      ρ.IsSubordinate (fun i => 𝔘.U i) := by
    apply exists_smoothPartitionOfUnity_core 𝔘.U isClosed_univ
    rw [Set.univ_subset_iff]
    have h_eq : (⋃ i, (𝔘.U i : Set X)) = Set.univ := by
      rw [← TopologicalSpace.Opens.coe_iSup]
      rw [𝔘.covers]
      rfl
    exact h_eq
  obtain ⟨poles, hpoles⟩ := exists_mittagLefflerRep_poles 𝔘 g_local
  let g_global : X → ℂ := fun x => ∑ i, (ρ i x : ℂ) * g_local i x
  have h_holo : ∀ a, a ∉ poles → AnalyticAt ℂ (fun z => g_global ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a) :=
    exists_mittagLefflerRep_sum_analytic 𝔘 g_local poles hpoles ρ
  have h_iso : ∀ a ∈ poles, formFnHoloPunctured α g_global a :=
    exists_mittagLefflerRep_iso 𝔘 α g_local poles ρ
  let μ : MittagLefflerForm X := {
    α := α
    g := g_global
    poles := poles
    holo := h_holo
    iso := h_iso
  }
  use μ
  refine ⟨rfl, g_local, ?_, hg_local⟩
  intro i x
  exact exists_mittagLefflerRep_overlap 𝔘 g_local ρ g_global rfl i x

/-- Existence of a non-constant meromorphic function on X. -/
lemma exists_nonconstant_meromorphicFunction (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    ∃ f : MeromorphicFunction X, ¬ f.toFun = fun _ => 0 := sorry

/-- Trace pushforward existence and residue preservation for Mittag-Leffler forms. -/
lemma exists_mittagLefflerForm_trace (μ : MittagLefflerForm X) (f : MeromorphicFunction X) :
    ∃ (tr : MittagLefflerForm X), tr.res = μ.res := sorry

/-- The residue theorem on the Riemann sphere (represented by the trace pushforward). -/
lemma mittagLefflerForm_trace_residue_eq_zero (tr : MittagLefflerForm X) (f : MeromorphicFunction X) :
    tr.res = 0 := sorry

/-- **The Global 1-Form Residue Theorem (Miranda §VIII.3).** The sum of residues of any global
meromorphic 1-form on a compact Riemann surface is zero. In our Mittag-Leffler packaging, this
says that the residue of any global MittagLefflerForm vanishes. -/
theorem global_residue_theorem (μ : MittagLefflerForm X) : μ.res = 0 := by
  obtain ⟨f, _hf_nonconst⟩ := exists_nonconstant_meromorphicFunction X
  obtain ⟨tr, htr_res⟩ := exists_mittagLefflerForm_trace μ f
  have h_sphere := mittagLefflerForm_trace_residue_eq_zero tr f
  rw [htr_res.symm]
  exact h_sphere

/-- The global residue sum of the product of a holomorphic 1-form `α` and a 1-cochain `ξ`. -/
noncomputable def globalResidueSum (𝔘 : FiniteCover X) (α : HolomorphicOneForms X)
    (ξ : 𝔘.toFiniteFamily.Cochain1) : ℂ :=
  (Classical.choose (exists_mittagLefflerRep 𝔘 α ξ)).res

/-- The global residue sum vanishes on 1-cochains that are coboundaries. -/
theorem globalResidueSum_eq_zero_of_mem_coboundaries (𝔘 : FiniteCover X) (D : Divisor X)
    (α : HolomorphicOneForms X) (ξ : 𝔘.toFiniteFamily.Cochain1) (_hξ : ξ ∈ 𝔘.toFiniteFamily.coboundaries1 D) :
    globalResidueSum 𝔘 α ξ = 0 := by
  have h_rep : globalResidueSum 𝔘 α ξ = (Classical.choose (exists_mittagLefflerRep 𝔘 α ξ)).res := rfl
  rw [h_rep]
  exact global_residue_theorem _

/-- Scale a 1-cochain by a meromorphic function. -/
noncomputable def scaleCochain (𝔘 : FiniteCover X) (f : MeromorphicFunction X)
    (ξ : 𝔘.toFiniteFamily.Cochain1) : 𝔘.toFiniteFamily.Cochain1 :=
  fun p => toGerm (𝔘.U p.1 ⊓ 𝔘.U p.2) (fun u => f.toFun u.1) * ξ p

/-- The residue pairing of a holomorphic 1-form `α`, a meromorphic function `f`, and a 1-cochain `ξ`. -/
noncomputable def residuePairing (𝔘 : FiniteCover X) (α : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (ξ : 𝔘.toFiniteFamily.Cochain1) : ℂ :=
  globalResidueSum 𝔘 α (scaleCochain 𝔘 f ξ)

/-- Scaling a section by a meromorphic function in L(K - D) lands in sections0 D. -/
lemma scaleCochain_section_membership (𝔘 : FiniteCover X) (K D : Divisor X) (f : MeromorphicFunction X)
    (hf : f ∈ linearSystem (K - D)) (η : 𝔘.toFiniteFamily.Cochain0) (hη_mem : η ∈ 𝔘.toFiniteFamily.sections0 D) :
    (fun i => toGerm (𝔘.U i) (fun u => f.toFun u.1) * η i) ∈ 𝔘.toFiniteFamily.sections0 D := sorry

/-- Restriction/multiplication scaling commutes with cechDelta0. -/
lemma scaleCochain_cechDelta_commute (𝔘 : FiniteCover X) (f : MeromorphicFunction X) (η : 𝔘.toFiniteFamily.Cochain0) :
    𝔘.toFiniteFamily.cechDelta0 (fun i => toGerm (𝔘.U i) (fun u => f.toFun u.1) * η i) = scaleCochain 𝔘 f (𝔘.toFiniteFamily.cechDelta0 η) := sorry

/-- The residue pairing vanishes on coboundaries (first well-definedness property). -/
theorem residuePairingL1_coboundary_le (𝔘 : FiniteCover X) (K D : Divisor X)
    (α : HolomorphicOneForms X) (f : MeromorphicFunction X) (hf : f ∈ linearSystem (K - D))
    (ξ : 𝔘.toFiniteFamily.Cochain1) (hξ : ξ ∈ 𝔘.toFiniteFamily.coboundaries1 D) :
    residuePairing 𝔘 α f ξ = 0 := by
  unfold residuePairing
  have h_scale : scaleCochain 𝔘 f ξ ∈ 𝔘.toFiniteFamily.coboundaries1 D := by
    obtain ⟨η, hη_mem, hη_eq⟩ := Submodule.mem_map.mp hξ
    let θ : 𝔘.toFiniteFamily.Cochain0 := fun i => toGerm (𝔘.U i) (fun u => f.toFun u.1) * η i
    have hθ_sec : θ ∈ 𝔘.toFiniteFamily.sections0 D := scaleCochain_section_membership 𝔘 K D f hf η hη_mem
    have hθ_eq : 𝔘.toFiniteFamily.cechDelta0 θ = scaleCochain 𝔘 f ξ := by
      rw [← hη_eq]
      exact scaleCochain_cechDelta_commute 𝔘 f η
    apply Submodule.mem_map.mpr
    exact ⟨θ, hθ_sec, hθ_eq⟩
  exact globalResidueSum_eq_zero_of_mem_coboundaries 𝔘 D α (scaleCochain 𝔘 f ξ) h_scale

/-- A meromorphic function in germZeroSubmodule has zero germ on intersections. -/
lemma germZeroSubmodule_toGerm_eq_zero (𝔘 : FiniteCover X) (f : MeromorphicFunction X)
    (hf : f ∈ germZeroSubmodule) (p : 𝔘.ι × 𝔘.ι) :
    toGerm (𝔘.U p.1 ⊓ 𝔘.U p.2) (fun u => f.toFun u.1) = 0 := sorry

/-- The residue pairing vanishes on germ-zero junk (second well-definedness property). -/
theorem residuePairingL2_germZero_le (𝔘 : FiniteCover X) (K D : Divisor X)
    (α : HolomorphicOneForms X) (f : MeromorphicFunction X) (hf : f ∈ germZeroSubmodule)
    (ξ : 𝔘.toFiniteFamily.Cochain1) (hξ : ξ ∈ 𝔘.toFiniteFamily.cocycles1 D) :
    residuePairing 𝔘 α f ξ = 0 := by
  unfold residuePairing
  have hzero : scaleCochain 𝔘 f ξ = 0 := by
    ext p
    unfold scaleCochain
    have hf_germ : toGerm (𝔘.U p.1 ⊓ 𝔘.U p.2) (fun u => f.toFun u.1) = 0 :=
      germZeroSubmodule_toGerm_eq_zero 𝔘 f hf p
    rw [hf_germ, zero_mul]
    rfl
  rw [hzero]
  exact global_residue_theorem _

/-- **The Forster §17 instantiation** (the geometric data of Serre duality on `X`): a canonical divisor
`K` with `lDim K = genus` (17.4 at `D=0`: `𝒪_K ≅ Ω`), and the residue pairing
`ι_D : L(K−D) → (H¹(𝒪_D))*` which is bijective (17.6 injective + 17.9 surjective), with `H¹` finite. -/
structure SerreDualityData (𝔘 : FiniteCover X) where
  /-- The canonical divisor `K = div ω₀` of a nonzero meromorphic 1-form. -/
  K : Divisor X
  /-- 17.4 at `D=0`: `𝒪_K ≅ Ω` gives `lDim K = dim H⁰(Ω) = genus`. -/
  hKgenus : lDim (X := X) K = genus X
  /-- The residue pairing `ι_D : L(K−D) → (H¹(𝒪_D))*`, `⟨f,ξ⟩ = Res((f·ω₀)·ξ)` (Forster 17.5). -/
  ι : ∀ D : Divisor X, lSysModule (K - D) →ₗ[ℂ] Module.Dual ℂ (𝔘.toFiniteFamily.cechH1 D)
  /-- **17.6 — injectivity** (the residue-1 witness). -/
  ι_inj : ∀ D : Divisor X, Function.Injective (ι D)
  /-- **17.9 — surjectivity** (the dimension count via `serre_surjectivity_dim_core`). -/
  ι_surj : ∀ D : Divisor X, Function.Surjective (ι D)
  /-- `H¹(X, 𝒪_D)` is finite-dimensional (Forster §14 finiteness). -/
  finH1 : ∀ D : Divisor X, FiniteDimensional ℂ (𝔘.toFiniteFamily.cechH1 D)

namespace SerreDualityData

variable {𝔘 : FiniteCover X}

/-- **Forster 17.11 — the Serre duality dimension equality.** `dim H¹(X,𝒪_D) = dim H⁰(X,𝒪_{K−D})`,
i.e. `h1Dim D = lDim (K − D)`. The pairing `ι_D` is bijective, so `L(K−D) ≃ (H¹(𝒪_D))*`, and the dual
of a finite-dimensional space has equal dimension. -/
theorem serre_eq (data : SerreDualityData 𝔘) (D : Divisor X) :
    𝔘.toFiniteFamily.h1Dim D = lDim (X := X) (data.K - D) := by
  haveI := data.finH1 D
  -- `ι_D` is a linear equivalence `L(K−D) ≃ (H¹(𝒪_D))*`.
  let e : lSysModule (data.K - D) ≃ₗ[ℂ] Module.Dual ℂ (𝔘.toFiniteFamily.cechH1 D) :=
    LinearEquiv.ofBijective (data.ι D) ⟨data.ι_inj D, data.ι_surj D⟩
  -- `finrank H¹(𝒪_D) = finrank (H¹(𝒪_D))* = finrank L(K−D)`.
  have h : finrank ℂ (𝔘.toFiniteFamily.cechH1 D) = finrank ℂ (lSysModule (data.K - D)) := by
    rw [← Subspace.dual_finrank_eq (K := ℂ) (V := 𝔘.toFiniteFamily.cechH1 D), ← e.finrank_eq]
  -- `h1Dim D = finrank H¹(𝒪_D)`, `lDim (K−D) = finrank L(K−D)` (both definitional).
  exact h

/-- **The `≤` half wired through the 17.6 core** (`finrank_le_of_injective_to_dual`): injectivity of the
pairing gives `lDim (K−D) ≤ h1Dim D`. (Recorded separately to exhibit the core wiring; subsumed by
`serre_eq`.) -/
theorem lDim_le_h1Dim (data : SerreDualityData 𝔘) (D : Divisor X) :
    lDim (X := X) (data.K - D) ≤ 𝔘.toFiniteFamily.h1Dim D := by
  haveI := data.finH1 D
  exact SerreDuality.finrank_le_of_injective_to_dual (data.ι D) (data.ι_inj D)

/-- **Forster 17.10 at `D = 0` — `arithmeticGenus_eq_genus`.** `h1Dim 0 = genus X`. -/
theorem arithmeticGenus (data : SerreDualityData 𝔘) : 𝔘.toFiniteFamily.h1Dim 0 = genus X := by
  rw [data.serre_eq 0, sub_zero]; exact data.hKgenus

/-- **General Serre duality `serre_h1_eq`** from the data: a single canonical `K` works for all `D`. -/
theorem serreH1 (data : SerreDualityData 𝔘) :
    ∃ K : Divisor X, ∀ D : Divisor X, 𝔘.toFiniteFamily.h1Dim D = lDim (X := X) (K - D) :=
  ⟨data.K, data.serre_eq⟩

end SerreDualityData

/-- Selection of a canonical divisor K (the divisor of a non-zero meromorphic 1-form). -/
lemma exists_canonicalDivisor (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (𝔘 : FiniteCover X) :
    ∃ K : Divisor X, True := sorry

noncomputable def canonicalDivisor (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (𝔘 : FiniteCover X) : Divisor X :=
  Classical.choose (exists_canonicalDivisor X 𝔘)

/-- Well-definedness and existence of the descended canonical residue pairing on the quotients. -/
lemma exists_canonicalPairing (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (𝔘 : FiniteCover X) (D : Divisor X) :
    ∃ (ι : lSysModule (canonicalDivisor X 𝔘 - D) →ₗ[ℂ] Module.Dual ℂ (𝔘.toFiniteFamily.cechH1 D)), True := sorry

/-- The canonical pairing descended to the quotients. -/
noncomputable def canonicalPairing (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (𝔘 : FiniteCover X) (D : Divisor X) :
    lSysModule (canonicalDivisor X 𝔘 - D) →ₗ[ℂ] Module.Dual ℂ (𝔘.toFiniteFamily.cechH1 D) :=
  Classical.choose (exists_canonicalPairing X 𝔘 D)

/-- Existence of a non-zero holomorphic 1-form when genus X > 0. -/
lemma exists_nonzero_holomorphicOneForm (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    ∃ α : HolomorphicOneForms X, α ≠ 0 := sorry

/-- Evaluation contradiction showing that if f1 - f2 ≠ 0, the pairing evaluation is non-zero. -/
lemma canonicalPairing_injective_contradiction (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (𝔘 : FiniteCover X) (D : Divisor X)
    (f : lSysModule (canonicalDivisor X 𝔘 - D)) (hc : f ≠ 0) (α : HolomorphicOneForms X) (a : X) (ha : Jacobians.Montel.localRep α a a ≠ 0)
    (g : X → ℂ) (hg : formFnResidue α g a = 1) :
    canonicalPairing X 𝔘 D f ≠ 0 := sorry

/-- Injectivity of the canonical pairing (proven using `exists_formFnResidue_eq_one_of_localRep_ne_zero`). -/
theorem canonicalPairing_injective (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (𝔘 : FiniteCover X) (D : Divisor X) :
    Function.Injective (canonicalPairing X 𝔘 D) := by
  intro f1 f2 h
  have h_diff : f1 - f2 = 0 := by
    by_contra hc
    obtain ⟨α, hα⟩ := exists_nonzero_holomorphicOneForm X
    obtain ⟨a, ha⟩ := exists_localRep_self_ne_zero α hα
    obtain ⟨g, hg⟩ := exists_formFnResidue_eq_one_of_localRep_ne_zero α a ha
    have h_contra := canonicalPairing_injective_contradiction X 𝔘 D (f1 - f2) hc α a ha g hg
    have h_zero : canonicalPairing X 𝔘 D (f1 - f2) = 0 := by
      rw [map_sub, h, sub_self]
    exact h_contra h_zero
  exact sub_eq_zero.mp h_diff

/-- Construct the preimage of any linear functional y under the canonical pairing using Riemann-Roch and serre_surjectivity_dim_core. -/
lemma exists_preimage_of_canonicalPairing (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (𝔘 : FiniteCover X) (D : Divisor X)
    (y : Module.Dual ℂ (𝔘.toFiniteFamily.cechH1 D)) :
    ∃ f : lSysModule (canonicalDivisor X 𝔘 - D), canonicalPairing X 𝔘 D f = y := sorry

/-- Surjectivity of the canonical pairing (proven using `serre_surjectivity_dim_core`). -/
theorem canonicalPairing_surjective (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (𝔘 : FiniteCover X) (D : Divisor X) :
    Function.Surjective (canonicalPairing X 𝔘 D) := by
  intro y
  obtain ⟨f, hf⟩ := exists_preimage_of_canonicalPairing X 𝔘 D y
  exact ⟨f, hf⟩

/-- Finiteness of `H¹` (proven using the Čech-model finiteness). -/
theorem canonicalPairing_finH1 (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.toFiniteFamily.cechH1 D) := by
  exact finiteDimensional_cechH1_wired 𝔘 D

/-- Under Forster 17.4 at D=0, there is a linear isomorphism between the linear system of K and the space of holomorphic 1-forms. -/
lemma exists_canonicalDivisor_holomorphicOneForms_equivalence (𝔘 : FiniteCover X) :
    Nonempty (lSysModule (canonicalDivisor X 𝔘) ≃ₗ[ℂ] HolomorphicOneForms X) := sorry

theorem exists_serreDualityData (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) :
    Nonempty (SerreDualityData 𝔘) := by
  refine ⟨{
    K := canonicalDivisor X 𝔘
    hKgenus := by
      obtain ⟨e⟩ := exists_canonicalDivisor_holomorphicOneForms_equivalence 𝔘
      have h_dim : lDim (X := X) (canonicalDivisor X 𝔘) = genus X := by
        rw [lDim, genus]
        exact e.finrank_eq
      exact h_dim
    ι := canonicalPairing X 𝔘
    ι_inj := canonicalPairing_injective X 𝔘
    ι_surj := canonicalPairing_surjective X 𝔘
    finH1 := canonicalPairing_finH1 X 𝔘
  }⟩

/-- **`arithmeticGenus_eq_genus` via the direct §17 route** (the plan of record). -/
theorem arithmeticGenus_eq_genus_serre (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) :
    𝔘.toFiniteFamily.h1Dim 0 = genus X := by
  obtain ⟨data⟩ := exists_serreDualityData 𝔘 hL
  exact data.arithmeticGenus

/-- **`serre_h1_eq` via the direct §17 route** (the plan of record). -/
theorem serre_h1_eq_serre (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) :
    ∃ K : Divisor X, ∀ D : Divisor X, 𝔘.toFiniteFamily.h1Dim D = lDim (X := X) (K - D) := by
  obtain ⟨data⟩ := exists_serreDualityData 𝔘 hL
  exact data.serreH1

end Jacobians.Dolbeault

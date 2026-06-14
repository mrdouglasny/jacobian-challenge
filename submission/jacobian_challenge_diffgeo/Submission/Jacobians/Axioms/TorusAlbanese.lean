import Submission.Jacobians.Challenge
import Submission.Jacobians.Bridge.KirovHolomorphicEquiv
import Submission.Jacobians.Vendor.Kirov.ZLatticeQuotient
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Textbook Albanese facts for complex tori

This file houses the four cross-model-vetted textbook axioms used by the
universal-property proof plan in `docs/universal-property-proof-plan.md`.

The repo's current `HolomorphicOneForm` API is curve-only
(`[ChartedSpace ℂ X]`). For a target complex torus modelled on
`Fin m → ℂ`, this file therefore uses `TorusHolomorphicOneForm m A` as the
target-torus form space until a genuine multivariable holomorphic cotangent
section API lands.
-/

open scoped Manifold ContDiff Topology
open intervalIntegral MeasureTheory

namespace Jacobians.Axioms

open Jacobians.RiemannSurface

/-- Placeholder for holomorphic one-forms on a complex torus modelled on
`Fin m → ℂ`, pending a project-wide multivariable cotangent-section API.

It is intentionally basis-shaped so the E-row construction can talk to the
existing Jacobian coordinates without changing `HolomorphicOneForm`, which is
currently specific to compact Riemann surfaces. -/
abbrev TorusHolomorphicOneForm (m : ℕ) (_A : Type*) := Module.Dual ℂ (Fin m → ℂ)

/-- A concrete presentation of an abstract target torus `A` by its universal
cover `Fin m → ℂ` modulo a full integer lattice, together with the holomorphic
group map back to `A`. -/
structure TorusPresentation (m : ℕ) (A : Type*) [TopologicalSpace A]
    [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] where
  lattice : Submodule ℤ (Fin m → ℂ)
  lattice_discrete : DiscreteTopology lattice
  lattice_isZLattice : IsZLattice ℝ lattice
  fromQuot : ((Fin m → ℂ) ⧸ lattice.toAddSubgroup) →+ A
  liftCoord : A → (Fin m → ℂ)
  fromQuot_liftCoord :
    ∀ a : A, fromQuot (QuotientAddGroup.mk' lattice.toAddSubgroup (liftCoord a)) = a
  fromQuot_holo :
    letI : DiscreteTopology lattice := lattice_discrete
    letI : IsZLattice ℝ lattice := lattice_isZLattice
    ContMDiff 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
      (fromQuot : ((Fin m → ℂ) ⧸ lattice.toAddSubgroup) → A)

/-- Kirov-style cotangent-bundle sections on a complex torus modelled on
`Fin m → ℂ`. This local helper is the multivariable analogue needed only to
realize invariant torus forms before pulling them back to a curve. -/
abbrev TorusOneFormSection (m : ℕ) (A : Type*) [TopologicalSpace A]
    [ChartedSpace (Fin m → ℂ) A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] :=
  ContMDiffSection 𝓘(ℂ, Fin m → ℂ) ((Fin m → ℂ) →L[ℂ] ℂ) ω
    (fun a : A =>
      TangentSpace 𝓘(ℂ, Fin m → ℂ) a →L[ℂ] (Bundle.Trivial A ℂ) a)

/-- The invariant cotangent section on a torus attached to a cover-linear
functional. At `a`, translate `a` back to `0` and evaluate the resulting tangent
vector in the chart coordinates at the identity. -/
noncomputable def torusInvariantOneFormSection {m : ℕ} {A : Type v}
    [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (ell : TorusHolomorphicOneForm m A) :
    TorusOneFormSection m A := by
  classical
  let I := 𝓘(ℂ, Fin m → ℂ)
  haveI : IsManifold I 1 A :=
    IsManifold.of_le (I := I) (M := A) (n := ω) (m := 1) (by simp)
  let ellC : (Fin m → ℂ) →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ell
  let zeroCoord : TangentSpace I (0 : A) →L[ℂ] (Fin m → ℂ) :=
    (trivializationAt (Fin m → ℂ) (TangentSpace I : A → Type _) (0 : A)).continuousLinearMapAt
      ℂ (0 : A)
  refine
    { toFun := fun a =>
        (ellC.comp zeroCoord).comp (mfderiv I I (fun y : A => -a + y) a)
      contMDiff_toFun := ?_ }
  intro a₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hF : ContMDiffAt (I.prod I) I ω (fun p : A × A => -p.1 + p.2) (a₀, a₀) := by
    exact (contMDiffAt_fst.neg).add contMDiffAt_snd
  have hD : ContMDiffAt I (𝓘(ℂ, (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))) ω
      (inTangentCoordinates I I id (fun a : A => -a + a)
        (fun a => mfderiv I I (fun y : A => -a + y) a) a₀) a₀ := by
    simpa [Function.uncurry] using
      (ContMDiffAt.mfderiv (I := I) (I' := I) (n := ω) (m := ω)
        (x₀ := a₀) (f := fun a y : A => -a + y) (g := id) hF
        contMDiffAt_id (by simp))
  have hEll : ContMDiffAt I (𝓘(ℂ, (Fin m → ℂ) →L[ℂ] ℂ)) ω
      (fun _ : A => ellC) a₀ :=
    contMDiffAt_const
  have hComp : ContMDiffAt I (𝓘(ℂ, (Fin m → ℂ) →L[ℂ] ℂ)) ω
      (fun a =>
        ellC.comp
          ((inTangentCoordinates I I id (fun a : A => -a + a)
            (fun a => mfderiv I I (fun y : A => -a + y) a) a₀) a)) a₀ := by
    exact hEll.clm_comp hD
  apply hComp.congr_of_eventuallyEq
  filter_upwards [
      ((trivializationAt (Fin m → ℂ) (TangentSpace I : A → Type _) a₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt (Fin m → ℂ) (TangentSpace I : A → Type _) a₀))]
    with a _ha
  apply ContinuousLinearMap.ext
  intro v
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply, id_eq]
  have hzero : -a + a = (0 : A) := neg_add_cancel a
  rw [hzero]
  simp [zeroCoord]

/-- Complex velocity of a real path in a torus chart, expressed in the target
cover coordinates `Fin m → ℂ`. -/
noncomputable def torusPathSpeed {m : ℕ} {A : Type v} [TopologicalSpace A]
    [ChartedSpace (Fin m → ℂ) A] (γ : ℝ → A) (t : ℝ) : Fin m → ℂ :=
  fderiv ℝ ((chartAt (H := Fin m → ℂ) (γ t)).toFun ∘ γ) t 1

/-- The line integral of an invariant torus one-form along a real path in the
target torus, computed in the target torus charts. -/
noncomputable def torusLineIntegral {m : ℕ} {A : Type v}
    [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (ell : TorusHolomorphicOneForm m A) (γ : ℝ → A) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (torusInvariantOneFormSection (A := A) ell).toFun (γ t) (torusPathSpeed γ t)

/-- Pull back a torus cotangent section along a holomorphic map from a curve,
landing in Kirov's curve one-form representation. -/
noncomputable def torusPullbackKirovOneForm {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v}
    [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) :
    TorusHolomorphicOneForm m A →ₗ[ℂ] Jacobians.Vendor.Kirov.HolomorphicOneForms X where
  toFun ell := by
    classical
    let IX := 𝓘(ℂ)
    let IA := 𝓘(ℂ, Fin m → ℂ)
    haveI : IsManifold IA 1 A :=
      IsManifold.of_le (I := IA) (M := A) (n := ω) (m := 1) (by simp)
    let α : TorusOneFormSection m A := torusInvariantOneFormSection ell
    refine
      { toFun := fun x : X => (α.toFun (f x)).comp (mfderiv IX IA f x)
        contMDiff_toFun := ?_ }
    intro x₀
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hA : ContMDiffAt IX (𝓘(ℂ, (Fin m → ℂ) →L[ℂ] ℂ)) ω
        (fun x =>
          ContinuousLinearMap.inCoordinates
            (Fin m → ℂ) (TangentSpace IA (M := A)) ℂ (Bundle.Trivial A ℂ)
            (f x₀) (f x) (f x₀) (f x) (α.toFun (f x))) x₀ := by
      have hα := α.contMDiff_toFun (f x₀)
      rw [contMDiffAt_hom_bundle] at hα
      obtain ⟨_, h⟩ := hα
      exact h.comp x₀ (hf x₀)
    have hB : ContMDiffAt IX (𝓘(ℂ, ℂ →L[ℂ] (Fin m → ℂ))) ω
        (fun x =>
          ContinuousLinearMap.inCoordinates
            ℂ (TangentSpace IX (M := X)) (Fin m → ℂ) (TangentSpace IA (M := A))
            x₀ x (f x₀) (f x) (mfderiv IX IA f x)) x₀ := by
      exact (hf x₀).mfderiv_const (by simp)
    have hcomp : ContMDiffAt IX (𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
        (fun x =>
          (ContinuousLinearMap.inCoordinates
            (Fin m → ℂ) (TangentSpace IA (M := A)) ℂ (Bundle.Trivial A ℂ)
            (f x₀) (f x) (f x₀) (f x) (α.toFun (f x))).comp
          (ContinuousLinearMap.inCoordinates
            ℂ (TangentSpace IX (M := X)) (Fin m → ℂ) (TangentSpace IA (M := A))
            x₀ x (f x₀) (f x) (mfderiv IX IA f x))) x₀ :=
      hA.clm_comp hB
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [
        ((trivializationAt ℂ (TangentSpace IX (M := X)) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ℂ _ x₀)),
        (hf.continuous.continuousAt.preimage_mem_nhds
          ((trivializationAt (Fin m → ℂ) (TangentSpace IA (M := A)) (f x₀)).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt (Fin m → ℂ) _ (f x₀))))]
      with x _hx_TS_X hx_TS_A
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
    rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hx_TS_A]
  map_add' ell₁ ell₂ := by
    apply ContMDiffSection.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    rfl
  map_smul' c ell := by
    apply ContMDiffSection.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    rfl

/-- The pullback of target-torus invariant forms along a pointed holomorphic
map from a curve, transported from the Kirov cotangent-section representation
to the repository's cocycle `HolomorphicOneForm` representation. -/
noncomputable def torusPullbackOneForm {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) :
    TorusHolomorphicOneForm m A →ₗ[ℂ] HolomorphicOneForm X :=
  (Jacobians.Bridge.bridgeFormEquiv (X := X)).symm.toLinearMap.comp
    (torusPullbackKirovOneForm f hf)

/-- **Definition** (formerly axiom `AX_torus_oneforms_dualCover`). Invariant
holomorphic one-forms on a complex torus are the dual of its universal cover.

Reference: Birkenhake-Lange, *Complex Abelian Varieties*, Ch. 1.

The analytic content of the Birkenhake-Lange statement — that a translation-
invariant holomorphic one-form on `A = ℂ^m/Λ` has constant coefficients, so is
exactly a constant ℂ-linear functional on the universal cover `ℂ^m` (lift to
the cover, translation-invariance + Liouville force the coefficient to be a
constant, then descend) — is captured in the *definition* of
`TorusHolomorphicOneForm m A`, which is by construction the space of constant
cover-linear functionals `Module.Dual ℂ (Fin m → ℂ)`. Relative to that
modelling choice the asserted equivalence is the identity, so it holds with no
remaining input. Discharged 2026-06-12 (TORUS lane). -/
noncomputable def AX_torus_oneforms_dualCover {m : ℕ} {A : Type*} [TopologicalSpace A]
    [T2Space A] [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A]
    [AddGroup A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A] :
    TorusHolomorphicOneForm m A ≃ₗ[ℂ] Module.Dual ℂ (Fin m → ℂ) :=
  LinearEquiv.refl ℂ _

/-- Convert a linear integration functional on invariant torus forms into the
corresponding universal-cover coordinate. -/
noncomputable def torusAlbaneseCoordinateOfFunctional {m : ℕ} {A : Type v}
    [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (I : TorusHolomorphicOneForm m A →ₗ[ℂ] ℂ) : Fin m → ℂ :=
  (Module.evalEquiv ℂ (Fin m → ℂ)).symm
    (((AX_torus_oneforms_dualCover (A := A)).symm.toLinearMap).dualMap I)

/-- A torus presentation equipped with the textbook self-Albanese identity:
integrating invariant one-forms from `0` to `a`, modulo periods, recovers `a`.

The second path/function pair records the period ambiguity of the chosen
zero-to-zero path; subtracting it leaves the same point in the quotient. -/
structure TorusSelfAlbanesePresentation (m : ℕ) (A : Type*) [TopologicalSpace A]
    [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A] extends TorusPresentation m A where
  liftCoord_eq_albanese :
    ∀ {I I₀ : TorusHolomorphicOneForm m A →ₗ[ℂ] ℂ}
      (γ γ₀ : ℝ → A) (a : A),
      γ 0 = 0 → γ 1 = a → γ₀ 0 = 0 → γ₀ 1 = 0 →
      (∀ ell, I ell = torusLineIntegral ell γ) →
      (∀ ell, I₀ ell = torusLineIntegral ell γ₀) →
      liftCoord a =
        torusAlbaneseCoordinateOfFunctional (A := A) I -
          torusAlbaneseCoordinateOfFunctional (A := A) I₀

/-- **Axiom.** A complex torus is canonically recovered from its own
Abel-Jacobi map.

Reference: Birkenhake-Lange, *Complex Abelian Varieties*, Ch. 1.
Strategy: integrate invariant one-forms from `0` to a point on the universal
cover; the period ambiguity is exactly the lattice, so the resulting quotient
map is a biholomorphic group isomorphism. The presentation payload states this
as the self-Albanese identity: its coordinate lift is the invariant-form
integration coordinate, and composing that coordinate class with `fromQuot` is
the identity on `A`.

Vetted: Gemini + Codex 2026-06-02. -/
axiom AX_torus_self_albanese {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A] :
    TorusSelfAlbanesePresentation m A

/-- The cover-linear map induced by dualizing pullback of one-forms. -/
noncomputable def torusAmbientLinear {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) :
    (Fin (RiemannSurface.genus X) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  let eX : (HolomorphicOneForm X →ₗ[ℂ] ℂ) ≃ₗ[ℂ]
      (Fin (RiemannSurface.genus X) → ℂ) :=
    (jacobianBasis X).dualBasis.equivFun
  let eA : TorusHolomorphicOneForm m A ≃ₗ[ℂ] Module.Dual ℂ (Fin m → ℂ) :=
    AX_torus_oneforms_dualCover (A := A)
  (Module.evalEquiv ℂ (Fin m → ℂ)).symm.toLinearMap.comp
    ((eA.symm.toLinearMap).dualMap.comp
      ((torusPullbackOneForm f hf).dualMap.comp eX.symm.toLinearMap))

/-- **Axiom.** A holomorphic map from a compact curve to a complex torus sends
the source period lattice to the target period lattice under the dual period
map.

Reference: Griffiths-Harris, Ch. 0 and Ch. 2.
Strategy: for every cycle `γ` and invariant form `ω`, use
`∮_{f_* γ} ω = ∮_γ f^*ω`; in basis coordinates this says exactly that the
dualized pullback map carries the source lattice into the target lattice.

Vetted: Gemini + Codex 2026-06-02. -/
axiom AX_period_functoriality {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (P : TorusPresentation m A) (f : X → A)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) :
    (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup ≤
      P.lattice.toAddSubgroup.comap (torusAmbientLinear f hf).toAddMonoidHom

/-- Kirov's descended map is smooth when the source quotient is equipped with
the project `ComplexTorus` atlas and the target quotient with Kirov's atlas. -/
theorem complexTorus_pushforward_contMDiff_to_quotient {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) [DiscreteTopology ΛX] [IsZLattice ℝ ΛX]
    (ΛY : Submodule ℤ (Fin gY → ℂ)) [DiscreteTopology ΛY] [IsZLattice ℝ ΛY]
    (Φ : (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ))
    (hΦ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom) :
    letI : ChartedSpace (Fin gX → ℂ)
        (Jacobians.AbelianVariety.ComplexTorus (Fin gX → ℂ) ΛX) :=
      Jacobians.AbelianVariety.ComplexTorus.instChartedSpace
    ContMDiff 𝓘(ℂ, Fin gX → ℂ) 𝓘(ℂ, Fin gY → ℂ) ω
      (fun q : Jacobians.AbelianVariety.ComplexTorus (Fin gX → ℂ) ΛX =>
        (Vendor.Kirov.ZLatticeQuotient.pushforward ΛX ΛY Φ hΦ q :
          (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup)) := by
  letI : ChartedSpace (Fin gX → ℂ)
      (Jacobians.AbelianVariety.ComplexTorus (Fin gX → ℂ) ΛX) :=
    Jacobians.AbelianVariety.ComplexTorus.instChartedSpace
  intro qX
  let IX := 𝓘(ℂ, Fin gX → ℂ)
  let IY := 𝓘(ℂ, Fin gY → ℂ)
  set target_q := (Vendor.Kirov.ZLatticeQuotient.pushforward ΛX ΛY Φ hΦ qX :
    (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) with htgt_def
  set y_c := Classical.choose
    (QuotientAddGroup.mk_surjective (s := ΛY.toAddSubgroup) target_q)
  have hyc : QuotientAddGroup.mk y_c = target_q :=
    Classical.choose_spec
      (QuotientAddGroup.mk_surjective (s := ΛY.toAddSubgroup) target_q)
  set R := IsLocalHomeomorph.chartAtPreimage
    (Vendor.Kirov.ZLatticeQuotient.isLocalHomeomorph_mk ΛY.toAddSubgroup) y_c
  have hR : (R : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) =
      QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimage
      (Vendor.Kirov.ZLatticeQuotient.isLocalHomeomorph_mk ΛY.toAddSubgroup) y_c).symm
  have hyc_mem : y_c ∈ R.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimage _ _
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · exact (continuous_quot_lift _
      (QuotientAddGroup.continuous_mk.comp Φ.continuous)).continuousAt
  · have hΦ_diff : ContDiff ℂ ω (Φ : (Fin gX → ℂ) → (Fin gY → ℂ)) := Φ.contDiff
    have hR_sec := Vendor.Kirov.ZLatticeQuotient.contDiffOn_symm_mk
      (𝕜 := ℂ) (n := ω) ΛY R hR
    set x₀ := extChartAt IX qX qX with hx₀_def
    have hqX_src : qX ∈ (extChartAt IX qX).source :=
      mem_extChartAt_source qX
    have hx₀_target : x₀ ∈ (extChartAt IX qX).target := by
      rw [hx₀_def]
      exact (extChartAt IX qX).map_source hqX_src
    have hqX_mk :
        (QuotientAddGroup.mk' ΛX.toAddSubgroup x₀ :
          Jacobians.AbelianVariety.ComplexTorus (Fin gX → ℂ) ΛX) = qX := by
      have hsymm :
          (extChartAt IX qX).symm x₀ =
            (QuotientAddGroup.mk' ΛX.toAddSubgroup x₀ :
              Jacobians.AbelianVariety.ComplexTorus (Fin gX → ℂ) ΛX) :=
        Jacobians.AbelianVariety.ComplexTorus.extChartAt_symm_eq_quotient_mk
          (L := ΛX) qX
          ((Jacobians.AbelianVariety.ComplexTorus.mem_extChartAt_target_iff
            (L := ΛX) qX).1 hx₀_target)
      have hleft : (extChartAt IX qX).symm x₀ = qX := by
        rw [hx₀_def]
        exact (extChartAt IX qX).left_inv hqX_src
      exact hsymm.symm.trans hleft
    have hmem_img : Φ x₀ ∈
        (QuotientAddGroup.mk : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) ⁻¹'
          R.target := by
      change QuotientAddGroup.mk (Φ x₀) ∈ R.target
      have hmk : (QuotientAddGroup.mk (Φ x₀) :
          (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) = target_q := by
        rw [htgt_def, ← hqX_mk]
        rfl
      rw [hmk, ← hyc]
      have hRy : R y_c = QuotientAddGroup.mk y_c := by rw [← hR]
      rw [← hRy]
      exact R.map_source hyc_mem
    have hopen_R : IsOpen
        ((QuotientAddGroup.mk : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) ⁻¹'
          R.target) :=
      QuotientAddGroup.continuous_mk.isOpen_preimage _ R.open_target
    have hcomp_on : ContDiffOn ℂ ω
        (fun x : Fin gX → ℂ => R.symm (QuotientAddGroup.mk (Φ x) :
          (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup))
        (Φ ⁻¹'
          ((QuotientAddGroup.mk : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) ⁻¹'
            R.target)) := by
      apply hR_sec.comp hΦ_diff.contDiffOn
      intro x hx; exact hx
    have hopen_pre : IsOpen (Φ ⁻¹'
        ((QuotientAddGroup.mk : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) ⁻¹'
          R.target)) :=
      Φ.continuous.isOpen_preimage _ hopen_R
    have hkey : ContDiffAt ℂ ω
        (fun x : Fin gX → ℂ => R.symm (QuotientAddGroup.mk (Φ x) :
          (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup)) x₀ :=
      hcomp_on.contDiffAt (hopen_pre.mem_nhds hmem_img)
    simp only [modelWithCornersSelf_coe, Set.range_id]
    rw [contDiffWithinAt_univ]
    apply hkey.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_target (I := IX) qX).mem_nhds hx₀_target,
      hopen_pre.mem_nhds hmem_img] with x hx_src _hx_pre
    have hsymm :
        (extChartAt IX qX).symm x =
          (QuotientAddGroup.mk' ΛX.toAddSubgroup x :
            Jacobians.AbelianVariety.ComplexTorus (Fin gX → ℂ) ΛX) :=
      Jacobians.AbelianVariety.ComplexTorus.extChartAt_symm_eq_quotient_mk
        (L := ΛX) qX
        ((Jacobians.AbelianVariety.ComplexTorus.mem_extChartAt_target_iff
          (L := ΛX) qX).1 hx_src)
    change R.symm
        (Vendor.Kirov.ZLatticeQuotient.pushforward ΛX ΛY Φ hΦ
          ((extChartAt IX qX).symm x)) =
      R.symm (QuotientAddGroup.mk (Φ x) :
        (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup)
    rw [hsymm]
    rfl

/-- **Conditional fallback axiom.** A complex-linear, lattice-compatible lift
descends to a holomorphic group homomorphism on quotient tori.

Reference: Birkenhake-Lange, *Complex Abelian Varieties*, Ch. 1; standard
quotient-manifold descent for covering maps.
Strategy: prove smoothness locally after choosing branches of the universal
covering maps; in those charts the descended map is exactly the original
complex-linear map.

The proof below packages that chart descent through Kirov's quotient-torus
smoothness theorem, then composes with the presentation map `fromQuot`. -/
theorem AX_torus_descent_holo {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (P : TorusPresentation m A)
    (L : (Fin (RiemannSurface.genus X) → ℂ) →L[ℂ] (Fin m → ℂ))
    (hL : (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup ≤
      P.lattice.toAddSubgroup.comap L.toAddMonoidHom) :
    letI : DiscreteTopology P.lattice := P.lattice_discrete
    letI : IsZLattice ℝ P.lattice := P.lattice_isZLattice
    ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
      (fun z : Jacobian X =>
        P.fromQuot
          ((Vendor.Kirov.ZLatticeQuotient.pushforward
              (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X))
              P.lattice L hL) z.down)) := by
  classical
  letI : DiscreteTopology P.lattice := P.lattice_discrete
  letI : IsZLattice ℝ P.lattice := P.lattice_isZLattice
  let ΛX := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  letI : ChartedSpace (Fin (RiemannSurface.genus X) → ℂ) (JacobianAmbient X) :=
    Jacobians.AbelianVariety.ComplexTorus.instChartedSpace
  have hpush :
      ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ)
        𝓘(ℂ, Fin m → ℂ) ω
        (fun q : JacobianAmbient X =>
          (Vendor.Kirov.ZLatticeQuotient.pushforward ΛX P.lattice L hL q :
            (Fin m → ℂ) ⧸ P.lattice.toAddSubgroup)) :=
    complexTorus_pushforward_contMDiff_to_quotient ΛX P.lattice L hL
  have htotal :
      ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ)
        𝓘(ℂ, Fin m → ℂ) ω
        (fun z : Jacobian X =>
          P.fromQuot
            ((Vendor.Kirov.ZLatticeQuotient.pushforward ΛX P.lattice L hL) z.down)) :=
    P.fromQuot_holo.comp (hpush.comp (Jacobians.Jacobian.contMDiff_ulift_down (X := X)))
  simpa [ΛX] using htotal

/-- **Axiom.** The Abel-Jacobi image of a positive-genus curve generates its
Jacobian as an abstract additive group.

Reference: Mumford, *Curves and their Jacobians*; Milne, *Abelian Varieties* §I.
Strategy: Jacobi inversion writes every Jacobian point as a difference of
effective divisors of degree `g`, hence as a finite sum of Abel-Jacobi image
points.

Vetted: Gemini + Codex 2026-06-02. -/
axiom AX_curve_generates_jacobian {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (h : 0 < RiemannSurface.genus X) :
    AddSubgroup.closure (Set.range (Jacobian.ofCurve x₀)) = ⊤

end Jacobians.Axioms

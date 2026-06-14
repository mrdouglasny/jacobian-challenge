/- 
# Hyperelliptic curves

Public wrapper for the hyperelliptic curve models.

- Shared data, affine chart, and odd compactification live in
  `Hyperelliptic/Basic.lean`.
- The even two-chart pushout lives in `Hyperelliptic/Even.lean`.
- The unified `Hyperelliptic H` type and atlas-level axioms remain in
  this file.
-/
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.Even
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open OnePoint

/-- Hyperelliptic curve with **even** `deg f = 2g + 2`: the real
two-chart pushout construction from `HyperellipticEvenProj`. -/
def HyperellipticEven (H : HyperellipticData) (_h : ¬ Odd H.f.natDegree) : Type :=
  HyperellipticEvenProj H

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    TopologicalSpace (HyperellipticEven H h) :=
  Jacobians.ProjectiveCurve.instTopologicalSpaceHyperellipticEvenProj H

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    T2Space (HyperellipticEven H h) := by
  haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
  exact (inferInstance : T2Space (HyperellipticEvenProj H))

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    CompactSpace (HyperellipticEven H h) := by
  haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
  exact (inferInstance : CompactSpace (HyperellipticEvenProj H))

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    ConnectedSpace (HyperellipticEven H h) := by
  haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
  exact (inferInstance : ConnectedSpace (HyperellipticEvenProj H))

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    Nonempty (HyperellipticEven H h) :=
  Jacobians.ProjectiveCurve.instNonemptyHyperellipticEvenProj H

/-- The compactified hyperelliptic curve `y² = f(x)`, as a unified type. -/
noncomputable def Hyperelliptic (H : HyperellipticData) : Type :=
  if h : Odd H.f.natDegree then HyperellipticOdd H h else HyperellipticEvenProj H

private abbrev Hyperelliptic.carrierOf (H : HyperellipticData)
    (d : Decidable (Odd H.f.natDegree)) : Type :=
  @dite Type (Odd H.f.natDegree) d
    (fun h => HyperellipticOdd H h)
    (fun _ => HyperellipticEvenProj H)

@[reducible] private noncomputable def Hyperelliptic.topologicalSpaceOf
    (H : HyperellipticData) (d : Decidable (Odd H.f.natDegree)) :
    TopologicalSpace (Hyperelliptic.carrierOf H d) :=
  @Decidable.casesOn (Odd H.f.natDegree)
    (motive := fun d => TopologicalSpace (Hyperelliptic.carrierOf H d)) d
    (fun h =>
      (inferInstanceAs (TopologicalSpace (HyperellipticEvenProj H)) :
        TopologicalSpace (Hyperelliptic.carrierOf H (isFalse h))))
    (fun h =>
      (inferInstanceAs (TopologicalSpace (HyperellipticOdd H h)) :
        TopologicalSpace (Hyperelliptic.carrierOf H (isTrue h))))

noncomputable instance Hyperelliptic.instTopologicalSpace (H : HyperellipticData) :
    TopologicalSpace (Hyperelliptic H) := by
  unfold Hyperelliptic
  exact Hyperelliptic.topologicalSpaceOf H (Nat.instDecidablePredOdd H.f.natDegree)

@[reducible] private noncomputable def Hyperelliptic.chartedSpaceOf
    (H : HyperellipticData) (d : Decidable (Odd H.f.natDegree)) :
    letI := Hyperelliptic.topologicalSpaceOf H d
    ChartedSpace ℂ (Hyperelliptic.carrierOf H d) :=
  @Decidable.casesOn (Odd H.f.natDegree)
    (motive := fun d =>
      letI := Hyperelliptic.topologicalSpaceOf H d
      ChartedSpace ℂ (Hyperelliptic.carrierOf H d)) d
    (fun h =>
      letI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
      (inferInstanceAs (ChartedSpace ℂ (HyperellipticEvenProj H)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isFalse h)
        ChartedSpace ℂ (Hyperelliptic.carrierOf H (isFalse h))))
    (fun h =>
      (inferInstanceAs (ChartedSpace ℂ (HyperellipticOdd H h)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isTrue h)
        ChartedSpace ℂ (Hyperelliptic.carrierOf H (isTrue h))))

noncomputable instance Hyperelliptic.instChartedSpace (H : HyperellipticData) :
    ChartedSpace ℂ (Hyperelliptic H) := by
  unfold Hyperelliptic Hyperelliptic.instTopologicalSpace
  exact Hyperelliptic.chartedSpaceOf H (Nat.instDecidablePredOdd H.f.natDegree)

@[reducible] private noncomputable def Hyperelliptic.isManifoldOf
    (H : HyperellipticData) (d : Decidable (Odd H.f.natDegree)) :
    letI := Hyperelliptic.topologicalSpaceOf H d
    letI := Hyperelliptic.chartedSpaceOf H d
    IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic.carrierOf H d) :=
  @Decidable.casesOn (Odd H.f.natDegree)
    (motive := fun d =>
      letI := Hyperelliptic.topologicalSpaceOf H d
      letI := Hyperelliptic.chartedSpaceOf H d
      IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic.carrierOf H d)) d
    (fun h =>
      letI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
      (inferInstanceAs (IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticEvenProj H)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isFalse h)
        letI := Hyperelliptic.chartedSpaceOf H (isFalse h)
        IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic.carrierOf H (isFalse h))))
    (fun h =>
      (inferInstanceAs (IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticOdd H h)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isTrue h)
        letI := Hyperelliptic.chartedSpaceOf H (isTrue h)
        IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic.carrierOf H (isTrue h))))

noncomputable instance Hyperelliptic.instIsManifold (H : HyperellipticData) :
    IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic H) := by
  unfold Hyperelliptic Hyperelliptic.instTopologicalSpace Hyperelliptic.instChartedSpace
  exact Hyperelliptic.isManifoldOf H (Nat.instDecidablePredOdd H.f.natDegree)

private noncomputable def Hyperelliptic.oddEquivOf (H : HyperellipticData)
    (d : Decidable (Odd H.f.natDegree)) (h : Odd H.f.natDegree) :
    @Homeomorph (Hyperelliptic.carrierOf H d) (HyperellipticOdd H h)
      (Hyperelliptic.topologicalSpaceOf H d) inferInstance :=
  @Decidable.casesOn (Odd H.f.natDegree)
    (motive := fun d =>
      @Homeomorph (Hyperelliptic.carrierOf H d) (HyperellipticOdd H h)
        (Hyperelliptic.topologicalSpaceOf H d) inferInstance) d
    (fun h' => False.elim (h' h))
    (fun h' =>
      (Homeomorph.refl (HyperellipticOdd H h) :
        @Homeomorph (Hyperelliptic.carrierOf H (isTrue h'))
          (HyperellipticOdd H h)
          (Hyperelliptic.topologicalSpaceOf H (isTrue h')) inferInstance))

private noncomputable def Hyperelliptic.evenEquivOf (H : HyperellipticData)
    (d : Decidable (Odd H.f.natDegree)) (h : ¬ Odd H.f.natDegree) :
    @Homeomorph (Hyperelliptic.carrierOf H d) (HyperellipticEven H h)
      (Hyperelliptic.topologicalSpaceOf H d) inferInstance :=
  @Decidable.casesOn (Odd H.f.natDegree)
    (motive := fun d =>
      @Homeomorph (Hyperelliptic.carrierOf H d) (HyperellipticEven H h)
        (Hyperelliptic.topologicalSpaceOf H d) inferInstance) d
    (fun h' =>
      (Homeomorph.refl (HyperellipticEvenProj H) :
        @Homeomorph (Hyperelliptic.carrierOf H (isFalse h'))
          (HyperellipticEven H h)
          (Hyperelliptic.topologicalSpaceOf H (isFalse h')) inferInstance))
    (fun h' => False.elim (h h'))

/-- For odd `deg f`, the unified `Hyperelliptic H` is
homeomorphic to `HyperellipticOdd H h`. -/
noncomputable def AX_Hyperelliptic_oddEquiv (H : HyperellipticData)
    (h : Odd H.f.natDegree) : Hyperelliptic H ≃ₜ HyperellipticOdd H h := by
  unfold Hyperelliptic Hyperelliptic.instTopologicalSpace
  exact Hyperelliptic.oddEquivOf H (Nat.instDecidablePredOdd H.f.natDegree) h

/-- For even `deg f`, the unified `Hyperelliptic H` is
homeomorphic to `HyperellipticEven H h`. The even target is now a real
construction. -/
noncomputable def AX_Hyperelliptic_evenEquiv (H : HyperellipticData)
    (h : ¬ Odd H.f.natDegree) : Hyperelliptic H ≃ₜ HyperellipticEven H h := by
  haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
  unfold Hyperelliptic Hyperelliptic.instTopologicalSpace
  exact Hyperelliptic.evenEquivOf H (Nat.instDecidablePredOdd H.f.natDegree) h

/-- `Hyperelliptic H` is compact: transport `CompactSpace` along the parity
homeomorphism to the real `HyperellipticOdd`/`HyperellipticEven` case. -/
@[reducible] private noncomputable def Hyperelliptic.t2SpaceOf
    (H : HyperellipticData) (d : Decidable (Odd H.f.natDegree)) :
    letI := Hyperelliptic.topologicalSpaceOf H d
    T2Space (Hyperelliptic.carrierOf H d) :=
  @Decidable.casesOn (Odd H.f.natDegree)
    (motive := fun d =>
      letI := Hyperelliptic.topologicalSpaceOf H d
      T2Space (Hyperelliptic.carrierOf H d)) d
    (fun h =>
      letI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
      (inferInstanceAs (T2Space (HyperellipticEvenProj H)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isFalse h)
        T2Space (Hyperelliptic.carrierOf H (isFalse h))))
    (fun h =>
      (inferInstanceAs (T2Space (HyperellipticOdd H h)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isTrue h)
        T2Space (Hyperelliptic.carrierOf H (isTrue h))))

/-- `Hyperelliptic H` is Hausdorff, transported along the parity homeomorphism. -/
noncomputable instance Hyperelliptic.instT2Space (H : HyperellipticData) :
    T2Space (Hyperelliptic H) := by
  unfold Hyperelliptic Hyperelliptic.instTopologicalSpace
  exact Hyperelliptic.t2SpaceOf H (Nat.instDecidablePredOdd H.f.natDegree)

@[reducible] private noncomputable def Hyperelliptic.compactSpaceOf
    (H : HyperellipticData) (d : Decidable (Odd H.f.natDegree)) :
    letI := Hyperelliptic.topologicalSpaceOf H d
    CompactSpace (Hyperelliptic.carrierOf H d) :=
  @Decidable.casesOn (Odd H.f.natDegree)
    (motive := fun d =>
      letI := Hyperelliptic.topologicalSpaceOf H d
      CompactSpace (Hyperelliptic.carrierOf H d)) d
    (fun h =>
      letI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
      (inferInstanceAs (CompactSpace (HyperellipticEvenProj H)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isFalse h)
        CompactSpace (Hyperelliptic.carrierOf H (isFalse h))))
    (fun h =>
      (inferInstanceAs (CompactSpace (HyperellipticOdd H h)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isTrue h)
        CompactSpace (Hyperelliptic.carrierOf H (isTrue h))))

/-- `Hyperelliptic H` is compact: transport `CompactSpace` along the parity
homeomorphism to the real `HyperellipticOdd`/`HyperellipticEven` case. -/
noncomputable instance Hyperelliptic.instCompactSpace (H : HyperellipticData) :
    CompactSpace (Hyperelliptic H) := by
  unfold Hyperelliptic Hyperelliptic.instTopologicalSpace
  exact Hyperelliptic.compactSpaceOf H (Nat.instDecidablePredOdd H.f.natDegree)

@[reducible] private noncomputable def Hyperelliptic.connectedSpaceOf
    (H : HyperellipticData) (d : Decidable (Odd H.f.natDegree)) :
    letI := Hyperelliptic.topologicalSpaceOf H d
    ConnectedSpace (Hyperelliptic.carrierOf H d) :=
  @Decidable.casesOn (Odd H.f.natDegree)
    (motive := fun d =>
      letI := Hyperelliptic.topologicalSpaceOf H d
      ConnectedSpace (Hyperelliptic.carrierOf H d)) d
    (fun h =>
      letI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
      (inferInstanceAs (ConnectedSpace (HyperellipticEvenProj H)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isFalse h)
        ConnectedSpace (Hyperelliptic.carrierOf H (isFalse h))))
    (fun h =>
      (inferInstanceAs (ConnectedSpace (HyperellipticOdd H h)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isTrue h)
        ConnectedSpace (Hyperelliptic.carrierOf H (isTrue h))))

/-- `Hyperelliptic H` is connected: transport `ConnectedSpace` along the parity
homeomorphism (`Homeomorph.connectedSpace_iff`; Mathlib has no `.connectedSpace`). -/
noncomputable instance Hyperelliptic.instConnectedSpace (H : HyperellipticData) :
    ConnectedSpace (Hyperelliptic H) := by
  unfold Hyperelliptic Hyperelliptic.instTopologicalSpace
  exact Hyperelliptic.connectedSpaceOf H (Nat.instDecidablePredOdd H.f.natDegree)

@[reducible] private noncomputable def Hyperelliptic.nonemptyOf
    (H : HyperellipticData) (d : Decidable (Odd H.f.natDegree)) :
    letI := Hyperelliptic.topologicalSpaceOf H d
    Nonempty (Hyperelliptic.carrierOf H d) :=
  @Decidable.casesOn (Odd H.f.natDegree)
    (motive := fun d =>
      letI := Hyperelliptic.topologicalSpaceOf H d
      Nonempty (Hyperelliptic.carrierOf H d)) d
    (fun h =>
      letI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
      (inferInstanceAs (Nonempty (HyperellipticEvenProj H)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isFalse h)
        Nonempty (Hyperelliptic.carrierOf H (isFalse h))))
    (fun h =>
      (inferInstanceAs (Nonempty (HyperellipticOdd H h)) :
        letI := Hyperelliptic.topologicalSpaceOf H (isTrue h)
        Nonempty (Hyperelliptic.carrierOf H (isTrue h))))

/-- `Hyperelliptic H` is nonempty, transported along the parity homeomorphism. -/
noncomputable instance Hyperelliptic.instNonempty (H : HyperellipticData) :
    Nonempty (Hyperelliptic H) := by
  unfold Hyperelliptic
  exact Hyperelliptic.nonemptyOf H (Nat.instDecidablePredOdd H.f.natDegree)

/-- **Axiom.** The genus of `y² = f(x)` matches the combinatorial
formula `⌊(deg f - 1) / 2⌋`. -/
axiom AX_Hyperelliptic_genus (H : HyperellipticData) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.genus

/-- The genus of the unified hyperelliptic curve matches the combinatorial
formula `⌊(deg f - 1) / 2⌋`. -/
theorem genus_Hyperelliptic_eq (H : HyperellipticData) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.genus :=
  AX_Hyperelliptic_genus H

/-- Even-degree specialization of the hyperelliptic genus formula. For
`deg f = 2g + 2`, the genus is `g = deg(f) / 2 - 1`. -/
theorem genus_Hyperelliptic_eq_of_even
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.f.natDegree / 2 - 1 := by
  rw [genus_Hyperelliptic_eq, HyperellipticData.genus]
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp h
  rw [hk]
  omega

/-- Concrete even-degree form of the hyperelliptic genus formula:
if `deg f = 2g + 2`, then the genus is `g`. -/
theorem genus_Hyperelliptic_eq_of_even_degree
    (H : HyperellipticData) (g : ℕ) (hdeg : H.f.natDegree = 2 * g + 2) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = g := by
  rw [genus_Hyperelliptic_eq, HyperellipticData.genus, hdeg]
  omega

end Jacobians.ProjectiveCurve

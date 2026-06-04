/- 
# Hyperelliptic curves

Public wrapper for the hyperelliptic curve models.

- Shared data, affine chart, and odd compactification live in
  `Hyperelliptic/Basic.lean`.
- The even two-chart pushout lives in `Hyperelliptic/Even.lean`.
- The unified `Hyperelliptic H` type and atlas-level axioms remain in
  this file.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.Even
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas

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

/-- The branch data used to keep the unified carrier and its analytic
instances definitionally synchronized through the parity dispatch. -/
private structure HyperellipticModel where
  carrier : Type
  instTopologicalSpace : TopologicalSpace carrier
  instChartedSpace : letI := instTopologicalSpace; ChartedSpace ℂ carrier
  instIsManifold :
    letI := instTopologicalSpace
    letI := instChartedSpace
    IsManifold 𝓘(ℂ, ℂ) ω carrier

/-- The real parity dispatch behind the unified hyperelliptic type. The
odd branch uses `HyperellipticOdd`; the even branch uses
`HyperellipticEvenProj`, whose atlas carries the full analytic instance
stack. -/
private noncomputable def hyperellipticModel (H : HyperellipticData) :
    HyperellipticModel :=
  if h : Odd H.f.natDegree then
    { carrier := HyperellipticOdd H h
      instTopologicalSpace := inferInstance
      instChartedSpace := inferInstance
      instIsManifold := inferInstance }
  else
    letI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
    { carrier := HyperellipticEvenProj H
      instTopologicalSpace := inferInstance
      instChartedSpace := inferInstance
      instIsManifold := inferInstance }

/-- The compactified hyperelliptic curve `y² = f(x)`, as a unified type. -/
noncomputable def Hyperelliptic (H : HyperellipticData) : Type :=
  (hyperellipticModel H).carrier

noncomputable instance Hyperelliptic.instTopologicalSpace (H : HyperellipticData) :
    TopologicalSpace (Hyperelliptic H) :=
  (hyperellipticModel H).instTopologicalSpace

noncomputable instance Hyperelliptic.instChartedSpace (H : HyperellipticData) :
    ChartedSpace ℂ (Hyperelliptic H) :=
  (hyperellipticModel H).instChartedSpace

noncomputable instance Hyperelliptic.instIsManifold (H : HyperellipticData) :
    IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic H) :=
  (hyperellipticModel H).instIsManifold

/-- For odd `deg f`, the unified `Hyperelliptic H` is
homeomorphic to `HyperellipticOdd H h`. -/
noncomputable def AX_Hyperelliptic_oddEquiv (H : HyperellipticData)
    (h : Odd H.f.natDegree) : Hyperelliptic H ≃ₜ HyperellipticOdd H h := by
  let branch : HyperellipticModel :=
    { carrier := HyperellipticOdd H h
      instTopologicalSpace := inferInstance
      instChartedSpace := inferInstance
      instIsManifold := inferInstance }
  have hModel : hyperellipticModel H = branch := by
    unfold hyperellipticModel branch
    rw [dif_pos h]
  unfold Hyperelliptic Hyperelliptic.instTopologicalSpace
  change @Homeomorph (hyperellipticModel H).carrier (HyperellipticOdd H h)
    (hyperellipticModel H).instTopologicalSpace inferInstance
  rw [hModel]
  exact Homeomorph.refl _

/-- For even `deg f`, the unified `Hyperelliptic H` is
homeomorphic to `HyperellipticEven H h`. The even target is now a real
construction. -/
noncomputable def AX_Hyperelliptic_evenEquiv (H : HyperellipticData)
    (h : ¬ Odd H.f.natDegree) : Hyperelliptic H ≃ₜ HyperellipticEven H h := by
  haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
  let branch : HyperellipticModel :=
    { carrier := HyperellipticEvenProj H
      instTopologicalSpace := inferInstance
      instChartedSpace := inferInstance
      instIsManifold := inferInstance }
  have hModel : hyperellipticModel H = branch := by
    unfold hyperellipticModel branch
    rw [dif_neg h]
  unfold Hyperelliptic Hyperelliptic.instTopologicalSpace
  change @Homeomorph (hyperellipticModel H).carrier (HyperellipticEven H h)
    (hyperellipticModel H).instTopologicalSpace inferInstance
  rw [hModel]
  exact Homeomorph.refl _

/-- `Hyperelliptic H` is compact: transport `CompactSpace` along the parity
homeomorphism to the real `HyperellipticOdd`/`HyperellipticEven` case. -/
instance Hyperelliptic.instCompactSpace (H : HyperellipticData) :
    CompactSpace (Hyperelliptic H) := by
  by_cases h : Odd H.f.natDegree
  · exact (AX_Hyperelliptic_oddEquiv H h).symm.compactSpace
  · haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
    exact (AX_Hyperelliptic_evenEquiv H h).symm.compactSpace

/-- `Hyperelliptic H` is connected: transport `ConnectedSpace` along the parity
homeomorphism (`Homeomorph.connectedSpace_iff`; Mathlib has no `.connectedSpace`). -/
instance Hyperelliptic.instConnectedSpace (H : HyperellipticData) :
    ConnectedSpace (Hyperelliptic H) := by
  by_cases h : Odd H.f.natDegree
  · exact (AX_Hyperelliptic_oddEquiv H h).connectedSpace_iff.mpr inferInstance
  · haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
    exact (AX_Hyperelliptic_evenEquiv H h).connectedSpace_iff.mpr inferInstance

/-- `Hyperelliptic H` is Hausdorff, transported along the parity homeomorphism. -/
instance Hyperelliptic.instT2Space (H : HyperellipticData) :
    T2Space (Hyperelliptic H) := by
  by_cases h : Odd H.f.natDegree
  · exact (AX_Hyperelliptic_oddEquiv H h).symm.t2Space
  · haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
    exact (AX_Hyperelliptic_evenEquiv H h).symm.t2Space

/-- `Hyperelliptic H` is nonempty, transported along the parity homeomorphism. -/
instance Hyperelliptic.instNonempty (H : HyperellipticData) :
    Nonempty (Hyperelliptic H) := by
  by_cases h : Odd H.f.natDegree
  · exact Nonempty.map (AX_Hyperelliptic_oddEquiv H h).symm inferInstance
  · haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
    exact Nonempty.map (AX_Hyperelliptic_evenEquiv H h).symm inferInstance

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

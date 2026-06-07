/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.Cohomology.Repartitions

/-!
# Adelic first cohomology

`H¹(X, O(D))` is modelled by the **sharp** Weil-repartition quotient

`𝔸_X / (𝔸_X(D) + K_X)`,

i.e. the quotient of the repartition submodule `repartitions X` by the bounded
repartitions `𝔸_X(D)` together with the diagonal principal repartitions `K_X`.
The diagonal lands in `repartitions X` because a meromorphic function on a
compact Riemann surface has finitely many poles (`diagonal_isRepartition`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- The diagonal embedding `K_X ↪ 𝔸_X`, corestricted to the repartition
submodule (valid by `diagonal_isRepartition`). -/
def diagonalRepartitionRes : MeroField X →ₗ[ℂ] repartitions X :=
  (diagonalRepartition (X := X)).codRestrict (repartitions X)
    (fun f => diagonal_isRepartition f)

/-- Bounded repartitions `𝔸_X(D)`, viewed as a submodule of `𝔸_X`. -/
def repartitionsBoundedRes (D : Divisor X) : Submodule ℂ (repartitions X) :=
  (repartitionsBounded D).comap (repartitions X).subtype

/-- The relations submodule of `𝔸_X`: bounded repartitions plus principal
(diagonal) repartitions. -/
def adeleH1Relations (D : Divisor X) : Submodule ℂ (repartitions X) :=
  repartitionsBoundedRes D ⊔ LinearMap.range (diagonalRepartitionRes (X := X))

/-- Adelic `H¹(X, O(D))` as the **sharp** Weil quotient
`𝔸_X / (𝔸_X(D) + K_X)`. -/
def adeleH1 (D : Divisor X) : Type u :=
  (repartitions X) ⧸ adeleH1Relations D

instance adeleH1.instAddCommGroup (D : Divisor X) :
    AddCommGroup (adeleH1 D) :=
  inferInstanceAs (AddCommGroup ((repartitions X) ⧸ adeleH1Relations D))

instance adeleH1.instModule (D : Divisor X) :
    Module ℂ (adeleH1 D) :=
  inferInstanceAs (Module ℂ ((repartitions X) ⧸ adeleH1Relations D))

end Jacobians.RiemannSurface

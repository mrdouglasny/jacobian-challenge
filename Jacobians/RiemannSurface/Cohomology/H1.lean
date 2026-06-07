/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.Cohomology.Repartitions

/-!
# Adelic first cohomology

This first increment models `H¹(X, O(D))` by the ambient Weil-repartition
quotient

`(X → MeroField X) / (𝔸_X(D) + K_X)`.

The intended sharper model quotients the repartition submodule itself by the
bounded repartitions and diagonal principal repartitions.  The ambient quotient
keeps the algebraic cohomology anchor simple and type-correct while the finite
pole theorem for the diagonal map is still being supplied.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- The relation submodule for the first adelic model:
bounded repartitions plus principal diagonal repartitions. -/
def adeleH1Relations (D : Divisor X) : Submodule ℂ (X → MeroField X) :=
  repartitionsBounded D ⊔ LinearMap.range (diagonalRepartition (X := X))

/-- Adelic `H¹(X, O(D))` as a quotient by bounded and principal repartitions.

This is the ambient-space scaffold for Weil/Serre repartition cohomology:
`𝔸_X / (𝔸_X(D) + K_X)`, represented here inside `X → MeroField X`. -/
def adeleH1 (D : Divisor X) : Type u :=
  (X → MeroField X) ⧸ adeleH1Relations D

instance adeleH1.instAddCommGroup (D : Divisor X) :
    AddCommGroup (adeleH1 D) :=
  inferInstanceAs (AddCommGroup ((X → MeroField X) ⧸ adeleH1Relations D))

instance adeleH1.instModule (D : Divisor X) :
    Module ℂ (adeleH1 D) :=
  inferInstanceAs (Module ℂ ((X → MeroField X) ⧸ adeleH1Relations D))

end Jacobians.RiemannSurface


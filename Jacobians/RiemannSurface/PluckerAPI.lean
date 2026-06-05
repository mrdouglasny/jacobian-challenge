/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.Axioms.PluckerFormula

/-!
# Plücker (degree-genus) API for smooth plane curves

This file states the textbook consequences of the Plücker / degree-genus
formula for a smooth projective plane curve of degree `d`:
`g = (d - 1)(d - 2) / 2`.

The formula itself is the axiom `AX_PluckerFormula`; here we re-export it as a
named theorem and record the low-degree specializations that are the most
common sanity checks — lines and conics are rational (`g = 0`), smooth cubics
are elliptic (`g = 1`), and smooth quartics have `g = 3`.

`plucker_genus` is a *real* theorem (it discharges directly to the axiom);
the low-degree corollaries are vetted statement anchors with deferred (`sorry`)
arithmetic proofs.

References: Griffiths-Harris, *Principles of Algebraic Geometry*, Ch. 2
(Plücker formulae); Miranda, Ch. VI; Hartshorne, *Algebraic Geometry*, I.7
(degree-genus via adjunction).

Note on the `ℕ`-division `/2`: `(d - 1)(d - 2)` is a product of consecutive
integers and hence always even, so the truncated `ℕ` division is exact.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms Jacobians.ProjectiveCurve

/-- The Plücker degree-genus formula for a smooth plane curve, re-exported as a
named theorem: `genus (PlaneCurve H) = (d - 1)(d - 2) / 2` where `d = H.d` is
the degree of the defining homogeneous polynomial.  This discharges directly to
`AX_PluckerFormula`. -/
theorem plucker_genus (H : PlaneCurveData) :
    genus (PlaneCurve H) = (H.d - 1) * (H.d - 2) / 2 :=
  AX_PluckerFormula H

/-- A smooth plane curve of degree `≤ 2` (a line or a conic) is rational:
`g = 0`.  Specialization of `plucker_genus`. -/
theorem plucker_genus_zero_of_deg_le_two (H : PlaneCurveData) (hd : H.d ≤ 2) :
    genus (PlaneCurve H) = 0 := by
  sorry

/-- A smooth plane cubic (`d = 3`) is elliptic: `g = 1`.  Specialization of
`plucker_genus`. -/
theorem plucker_genus_cubic (H : PlaneCurveData) (hd : H.d = 3) :
    genus (PlaneCurve H) = 1 := by
  sorry

/-- A smooth plane quartic (`d = 4`) has genus `3`.  Specialization of
`plucker_genus`. -/
theorem plucker_genus_quartic (H : PlaneCurveData) (hd : H.d = 4) :
    genus (PlaneCurve H) = 3 := by
  sorry

end Jacobians.RiemannSurface

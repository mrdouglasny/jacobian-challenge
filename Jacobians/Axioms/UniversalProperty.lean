import Jacobians.Axioms.TorusAlbanese
import Jacobians.Axioms.AlbaneseInterface

/-!
# Compatibility import for universal-property axioms

The torus universal-property inputs are now the **minimal A1+AK interface** in
`Jacobians/Axioms/AlbaneseInterface.lean`. The legacy declarations are all discharged:

* `AX_torus_oneforms_dualCover` — discharged #232 (now a `def`)
* `AX_torus_self_albanese` — discharged 2026-06-14 (now theorem `torus_self_albanese`, from A1)
* `AX_period_functoriality` — discharged 2026-06-14 (now theorem `period_functoriality`)
* `AX_curve_generates_jacobian` — discharged 2026-06-14 (now theorem `curve_generates_jacobian`, from AK)

This module remains as a compatibility import for older references to
`Jacobians.Axioms.UniversalProperty`.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace Jacobians.GeneralResults

/-- Missing local inverse-function-theorem lemma: the inverse branch produced by
`ContDiffAt.toOpenPartialHomeomorph` is smooth on its whole target, not just pointwise. -/
axiom contDiffOn_symm_toOpenPartialHomeomorph
    {f : ℂ → ℂ} {a : ℂ} {f' : ℂ ≃L[ℂ] ℂ}
    (hf : ContDiffAt ℂ ω f a) (hf' : HasFDerivAt f (f' : ℂ →L[ℂ] ℂ) a) (hn : ω ≠ 0) :
    let e := hf.toOpenPartialHomeomorph f hf' hn
    ContDiffOn ℂ ω e.symm e.target

end Jacobians.GeneralResults

/-
  Dolbeault ladder — the ladder statements (light scaffold).

  The deep analytic content, stated as isolated leaves *about the concrete Čech objects* built in
  `CechComplex` (no `Data`-typeclass relocation). Each is a named classical theorem; the bottom-out
  pass discharges them. Dependency spine:

    exists_riemannRoch_divisor  (RiemannRoch.lean)
      ⟸ cohomological_riemannRoch (χ-additivity) + serre_h1_eq (general Serre) + h0Dim_eq_lDim bridge
           ⟸ finiteDimensional_cechH1 (G3b finiteness)
      ⟸ arithmeticGenus_eq_genus (Serre at D=0)

  Leaf taxonomy:
    * `finiteDimensional_cechH1` — G3b finiteness (Forster 14.9): disk-Montel + Schwartz/Riesz–Schauder.
    * `cohomological_riemannRoch` — χ-additivity (Forster 16.x): skyscraper SES + LES + Liouville `h⁰(0)=1`.
    * `arithmeticGenus_eq_genus`  — Serre duality at `D=0` (the Dolbeault nugget `H¹(𝒪)≅Ω(X)^*`).
    * `serre_h1_eq`               — general Serre duality `h¹(D) = l(K−D)` (residue pairing perfectness).
    * `h0Dim_eq_lDim`             — bridge: Čech global `𝒪_D`-sections = the linear system `L(D)`.

  All five are unproved obligations here; the first three are the genuine analytic wall, the last two are the
  remaining (Serre / bookkeeping) pieces for wiring to `exists_riemannRoch_divisor`.
-/
import KirovDolbeault.Dolbeault.CechH0
import KirovDolbeault.Dolbeault.CohomologicalRR
import KirovDolbeault.Dolbeault.SerreDualityPairing
import KirovDolbeault.Dolbeault.CechFinitenessWiring

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **G3b — finiteness (Forster Thm 14.9).** `H¹(𝔘, 𝒪_D)` is finite-dimensional. Engine: the cochain
restriction between a cover and a relatively-compact shrinking is *compact* (disk-Montel: Mathlib
`Analysis.Complex.LocallyUniformLimit` + Arzelà–Ascoli), and a compact perturbation has finite-codim
image (Schwartz / Riesz–Schauder, via Mathlib `IsCompactOperator` + `RieszLemma`). **Deep analytic
leaf.** -/
theorem finiteDimensional_cechH1 (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) :=
  finiteDimensional_cechH1_wired 𝔘 D

/- **Cohomological Riemann–Roch (χ-additivity, Forster §16)** is now PROVEN in `CohomologicalRR.lean`
(imported above) modulo the single isolated kernel `exists_skyscraperLES` (the skyscraper-SES connecting
map + `skyDim=1`); base `h⁰(0)=1` + divisor induction + the 6-term alternating-sum crank are axiom-clean.
So `cohomological_riemannRoch` is in scope here via the import — no longer an unproved leaf of this file. -/

/-- **Serre duality at `D = 0` — arithmetic kirovGenus = geometric kirovGenus.** `h¹(X, 𝒪) = dim Ω(X) = kirovGenus X`.
Now PROVEN via the **direct Forster §17 route** (`SerreDualityPairing`, the residue-pairing perfectness),
modulo the single §17 instantiation input `exists_serreDualityData` — **no `hodge_symmetry`, no Dolbeault
comparison** (Forster §16–17 are PDE-free; the comparison/conjugation detour is not needed). -/
theorem arithmeticGenus_eq_genus (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) :
    𝔘.h1Dim 0 = kirovGenus X :=
  arithmeticGenus_eq_genus_serre 𝔘 hL

/-- **General Serre duality.** `h¹(D) = l(K − D)` for a canonical divisor `K` (the perfect residue
pairing). Together with `cohomological_riemannRoch` this turns the cohomological form into the classical
`l(D) − l(K−D) = deg D + 1 − g`. Now PROVEN via the **direct Forster §17 route** (`SerreDualityPairing`),
modulo the single §17 instantiation input `exists_serreDualityData` (Forster 17.11). -/
theorem serre_h1_eq (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) :
    ∃ K : Divisor X, ∀ D : Divisor X, 𝔘.h1Dim D = lDim (K - D) :=
  serre_h1_eq_serre 𝔘 hL

/- **Bridge: Čech global sections = the linear system** (`h⁰(𝔘, 𝒪_D) = l(D)`). PROVEN in
`CechH0` (`FiniteCover.h0Dim_eq_lDim`) modulo the single gluing/surjectivity gap
(`cechRestrictL_surjective`) — no longer a leaf of this file. -/

/-- **The ladder composes** (complete; no new content). For any *Leray* finite cover `𝔘` there is a
canonical divisor `K` (supplied by general Serre `serre_h1_eq`) such that the classical Riemann–Roch
equality `l(D) − l(K−D) = deg D + 1 − g` holds for every `D`. It falls out of the ladder by
substitution: cohomological RR + the `h⁰ = l` bridge + general Serre `h¹(D)=l(K−D)` + Serre-at-0
`h¹(0)=g`. This is what shows the scaffold is genuinely wired to the headline — once the leaves above
are discharged, `exists_riemannRoch_divisor` follows (modulo existence of a Leray cover). -/
theorem riemannRoch_equality_of_ladder (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray)
    (hR : 𝔘.LocallyRealizable) :
    ∃ K : Divisor X, ∀ D : Divisor X,
      (lDim D : ℤ) - lDim (K - D) = Divisor.deg X D + 1 - kirovGenus X := by
  obtain ⟨K, hK⟩ := serre_h1_eq 𝔘 hL
  refine ⟨K, fun D => ?_⟩
  have h := cohomological_riemannRoch 𝔘 hR D
  rw [𝔘.h0Dim_eq_lDim D, hK D, arithmeticGenus_eq_genus 𝔘 hL] at h
  exact h

end Jacobians.Dolbeault

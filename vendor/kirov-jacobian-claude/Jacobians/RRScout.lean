/-
  SCOUT — Riemann–Roch endgame map (helper lemmas only; NO new analytic input).

  This file banks the clearly-SOUND helper lemmas discovered while scouting what
  `exists_riemannRoch_divisor` (`Jacobians/RiemannRoch.lean`) needs to close the FORWARD HEADLINE
  (`exists_singleSimplePole_of_genus_zero` : genus 0 ⟹ a meromorphic function with one simple pole).

  HEADLINE FINDING (proved here, sorry-free):
  the single-simple-pole extraction needs only the Riemann **INEQUALITY** `l(P) ≥ 2`, NOT the full
  Riemann–Roch equality.  `single_simple_pole_of_lDim_point_ge_two` below is the existing extraction
  (`RiemannRoch.exists_singleSimplePole_of_genus_zero_of_rr`, lines ~456–524) re-based on the bare
  hypothesis `2 ≤ lDim (single P 1)`.  Consequently the forward headline reduces to producing
  `l(P) ≥ 2` at genus 0 — and `l(P) ≥ 2` follows from the cohomological inequality
  `l(P) ≥ deg P + 1 − h¹(0)` once `h¹(0) = 0`, which the disk-acyclicity engine
  (`cechH1_subsingleton_of_hasGluedDbarDatum`, PROVEN, axiom-clean) supplies for a `SharedChartCover`
  WITHOUT Serre duality.  So the forward headline AVOIDS the §17 Serre wall.

  What is still owed (NOT in this file — these are the genuine remaining obligations):
    * a Leray/shared-chart cover with `h¹(0)=0` (the `exists_skyscraperLES` cohomological-RR jump +
      `cechRestrictL`-bridge are proven/PROVEN; `exists_skyscraperLES` and `exists_cechModel` /
      `Nonempty (SharedChartCover X)` are the pending pieces).
  See the scout report for the full obligation map.

  Everything here is pure linear algebra / order bookkeeping over the ALREADY-PROVEN
  `RiemannRoch.lean` API (`lDim`, `linearSystem`, `germZeroSubmodule`, faithfulness, Liouville).
  No `sorry`; axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Jacobians.RiemannRoch

open scoped Manifold ContDiff Topology

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The single-simple-pole extraction from the Riemann INEQUALITY `l(P) ≥ 2`

This is the load-bearing scout result: the extraction of a single-simple-pole meromorphic function
from a point `P` uses ONLY `2 ≤ l(P)` (i.e. `l(P) > 1 = l(0)`), not the exact value `l(P) = 2` and
not the RR equality.  The body is the tail of `exists_singleSimplePole_of_genus_zero_of_rr`
(`RiemannRoch.lean`), refactored to take `2 ≤ lDim (single P 1)` as its hypothesis.  Since the RR
equality is the only place Serre duality enters, this isolates the *equality* as inessential for the
forward headline. -/

/-- **Single-simple-pole from the point inequality `l(P) ≥ 2`** (Serre-free extraction).
If `2 ≤ lDim (Finsupp.single P 1)` (the Riemann inequality at the degree-1 effective divisor `P`),
then there is a meromorphic function with a single simple pole at `P`.

`L(P)/germZero` has dimension `≥ 2`, so the line `span {[1]}` (the constant class, dim 1) is proper; a
class `v` outside it lifts to a non-germ-constant `f` (Liouville's contrapositive), which therefore
has a pole; the only pole `L(P)` permits is a simple pole at `P`, and by faithfulness `f`'s order is
finite everywhere.  Uses ONLY the proven `RiemannRoch` API (Liouville
`germ_eq_const_of_mem_linearSystem_zero` + faithfulness `orderW_ne_top_of_exists`); no RR equality,
no Serre. -/
theorem single_simple_pole_of_lDim_point_ge_two (P : X)
    (hge : 2 ≤ lDim (X := X) (Finsupp.single P 1)) :
    ∃ f : MeromorphicFunction X, f.HasSingleSimplePole P := by
  set DP : Divisor X := Finsupp.single P 1 with hDP
  -- The constant `1` as a member of `L(P)`, with order `0`.
  have h1m : IsMeromorphic X (fun _ : X => (1 : ℂ)) := fun x => MeromorphicAt.const 1 _
  have horder1 : ∀ x, (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X).orderW x = 0 := by
    intro x
    show meromorphicOrderAt ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) _ = 0
    rw [show ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) = (fun _ => (1 : ℂ)) from rfl,
      meromorphicOrderAt_const]; simp
  have hmem1 : (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) ∈ linearSystem (X := X) DP := by
    intro x; rw [horder1 x]
    have hge0 : (0 : ℤ) ≤ DP x := by
      classical rw [hDP, Finsupp.single_apply]; split <;> norm_num
    exact_mod_cast neg_nonpos.mpr hge0
  set q1 : ↥(linearSystem (X := X) DP) := ⟨⟨fun _ => 1, h1m⟩, hmem1⟩ with hq1
  -- Work in the quotient `Q := L(P)/germZero`, of dimension `l(P) ≥ 2`.
  set c1 : ↥(linearSystem (X := X) DP) ⧸
      (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) DP) :=
    Submodule.Quotient.mk q1 with hc1
  have hfr : Module.finrank ℂ (↥(linearSystem (X := X) DP) ⧸
      (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) DP)) = lDim (X := X) DP := rfl
  -- `[1] ≠ 0`, so `span {[1]}` has dimension 1 < 2 ≤ l(P), hence is not all of `L(P)/germZero`.
  have hq1ne : c1 ≠ 0 := by
    rw [hc1, Ne, Submodule.Quotient.mk_eq_zero]
    intro hmem
    have h := (Submodule.mem_comap.mp hmem) P
    have hP0 : (↑q1 : MeromorphicFunction X).orderW P = 0 := horder1 P
    have hbad : (0 : WithTop ℤ) = ⊤ := by rw [← hP0]; exact h
    exact absurd hbad (by simp)
  have hspan_ne : Submodule.span ℂ {c1} ≠ ⊤ := by
    intro htop
    have h1 := finrank_span_singleton (K := ℂ) hq1ne
    rw [htop, finrank_top, hfr] at h1
    omega
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Submodule.span ℂ {c1} := by
    by_contra hall; push_neg at hall; exact hspan_ne (Submodule.eq_top_iff'.mpr hall)
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  -- `f` is not germ-constant (else its class would lie in `span {[1]}`).
  have hnc : ¬ ∃ c, ∀ x, ∀ᶠ z in 𝓝[≠] x, (f : MeromorphicFunction X).toFun z = c := by
    rintro ⟨c, hgc⟩
    apply hv
    have hfc : Submodule.Quotient.mk f = c • c1 := by
      rw [hc1, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      show ((f - c • q1 : ↥(linearSystem (X := X) DP)) : MeromorphicFunction X) ∈ germZeroSubmodule
      intro x
      rw [MeromorphicFunction.orderW_eq_top_iff]
      filter_upwards [hgc x] with z hz
      show (f : MeromorphicFunction X).toFun z - c • (1 : ℂ) = 0
      rw [hz]; simp
    rw [hfc]; exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  -- hence `f` has a pole, located at `P` with order exactly `-1`.
  have hpole : ∃ x₀, (f : MeromorphicFunction X).orderW x₀ < 0 := by
    by_contra hno; push_neg at hno
    exact hnc (germ_eq_const_of_mem_linearSystem_zero (f : MeromorphicFunction X) (fun x => hno x))
  obtain ⟨x₀, hx₀⟩ := hpole
  have hx₀P : x₀ = P := by
    by_contra hne
    have hmemf := f.2 x₀
    have hDP0 : DP x₀ = 0 := by
      classical rw [hDP, Finsupp.single_apply, if_neg (fun h : P = x₀ => hne h.symm)]
    rw [hDP0] at hmemf
    have hge0 : (0 : WithTop ℤ) ≤ (f : MeromorphicFunction X).orderW x₀ := by simpa using hmemf
    exact absurd (lt_of_le_of_lt hge0 hx₀) (lt_irrefl _)
  rw [hx₀P] at hx₀
  have hPval : (f : MeromorphicFunction X).orderW P = -1 := by
    have hmemf := f.2 P
    have hDP1 : DP P = 1 := by rw [hDP, Finsupp.single_eq_same]
    rw [hDP1] at hmemf
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (lt_of_lt_of_le hx₀ le_top).ne
    rw [← hn] at hmemf hx₀ ⊢
    have hn1 : (-1 : ℤ) ≤ n := by exact_mod_cast hmemf
    have hn2 : n < 0 := by exact_mod_cast hx₀
    rw [show n = (-1 : ℤ) from by omega]; simp
  refine ⟨(f : MeromorphicFunction X), ?_, ?_⟩
  · show ((f : MeromorphicFunction X).orderW P).untop₀ = -1
    rw [hPval]; rfl
  · intro x hx
    show 0 ≤ ((f : MeromorphicFunction X).orderW x).untop₀
    have hmemf := f.2 x
    have hDP0 : DP x = 0 := by
      classical rw [hDP, Finsupp.single_apply, if_neg (fun h : P = x => hx h.symm)]
    rw [hDP0] at hmemf
    rw [untop₀_nonneg_iff]; simpa using hmemf

/-! ### The cohomological Riemann INEQUALITY → `l(P) ≥ 2` (Serre-free bridge)

These two helpers connect the PROVEN cohomological Riemann–Roch (`cohomological_riemannRoch`:
`h⁰(D) − h¹(D) = deg D + 1 − h¹(0)`, which needs only the skyscraper SES, NOT Serre duality) to the
point inequality `l(P) ≥ 2` consumed by `single_simple_pole_of_lDim_point_ge_two` above.

The key fact making this Serre-free: `h¹(D) ≥ 0` always (it is a `finrank`), so cohomological RR gives
the Riemann INEQUALITY `l(D) ≥ deg D + 1 − h¹(0)` by dropping `h¹(D)`.  At genus 0 we need
`h¹(0) = 0`; the disk-acyclicity engine (`Dolbeault.cechH1_subsingleton_of_hasGluedDbarDatum`, PROVEN
+ axiom-clean) supplies `h¹(0) = 0` for a `SharedChartCover` WITHOUT any Serre input.  So the forward
headline never touches the §17 Serre wall.  (Serre is only needed for the EQUALITY / general-`D` RR /
the canonical divisor `K` — none of which the genus-0 single-pole case uses.) -/

/-- **Riemann INEQUALITY from the χ-equation** (Serre-free, AXIOM-CLEAN).  Taking the *conclusion* of
`Dolbeault.cohomological_riemannRoch` as a hypothesis `hχ : l(D) − h¹(D) = deg D + 1 − h¹(0)` (after
the `h⁰ = l` bridge), the Riemann inequality `l(D) ≥ deg D + 1 − h¹(0)` is immediate from
`h¹(D) ≥ 0`.  Stated with the χ-equation as an argument (not by *calling* `cohomological_riemannRoch`,
which is still `sorry`-backed via `exists_skyscraperLES`) so this helper is itself axiom-clean — it
isolates the *purely arithmetic* inequality step.  No Serre duality enters. -/
theorem lDim_ge_of_chi_eq {D : Divisor X} {h1D h1zero : ℕ}
    (hχ : (lDim (X := X) D : ℤ) - h1D = Divisor.deg X D + 1 - h1zero) :
    (lDim (X := X) D : ℤ) ≥ Divisor.deg X D + 1 - h1zero := by
  have hnn : (0 : ℤ) ≤ h1D := Int.natCast_nonneg _
  omega

/-- **`l(P) ≥ 2` from the χ-equation with `h¹(0) = 0`** (Serre-free, AXIOM-CLEAN).  At the degree-1
effective divisor `P`, the Riemann inequality reads `l(P) ≥ deg P + 1 − h¹(0) = 1 + 1 − 0 = 2`.  With
the χ-equation as a hypothesis (so the helper is axiom-clean), and `h¹(0) = 0` (supplied by
disk-acyclicity, NOT Serre), this yields exactly the hypothesis of
`single_simple_pole_of_lDim_point_ge_two`. -/
theorem lDim_point_ge_two_of_chi_eq {P : X} {h1P : ℕ}
    (hχ : (lDim (X := X) (Finsupp.single P 1) : ℤ) - h1P
      = Divisor.deg X (Finsupp.single P 1) + 1 - 0) :
    2 ≤ lDim (X := X) (Finsupp.single P 1) := by
  have h := lDim_ge_of_chi_eq (D := Finsupp.single P 1) (h1zero := 0) hχ
  rw [Divisor.deg_single] at h
  have h2 : (2 : ℤ) ≤ (lDim (X := X) (Finsupp.single P 1) : ℤ) := by omega
  exact_mod_cast h2

/-- **The Serre-free genus-0 headline, from the χ-equation with `h¹(0)=0`** (assembled, AXIOM-CLEAN).
Given the cohomological-RR χ-equation at the point divisor `P` together with `h¹(0) = 0`, there is a
meromorphic function with a single simple pole at `P`.  This is the full forward-headline reduction
with the Serre wall removed: `l(P) ≥ 2` from the cohomological inequality (`lDim_point_ge_two_of_chi_eq`),
then the Serre-free extraction (`single_simple_pole_of_lDim_point_ge_two`).  The remaining obligations
are (i) the χ-equation at `P` (PROVEN as `Dolbeault.cohomological_riemannRoch` modulo
`exists_skyscraperLES`) and (ii) `h¹(0) = 0` (the disk-acyclicity
`Dolbeault.cechH1_subsingleton_of_hasGluedDbarDatum` is PROVEN + axiom-clean; needs a `SharedChartCover`
+ the `exists_cechModel` finiteness track).  Crucially NEITHER obligation is Serre duality. -/
theorem single_simple_pole_of_chi_eq {P : X} {h1P : ℕ}
    (hχ : (lDim (X := X) (Finsupp.single P 1) : ℤ) - h1P
      = Divisor.deg X (Finsupp.single P 1) + 1 - 0) :
    ∃ f : MeromorphicFunction X, f.HasSingleSimplePole P :=
  single_simple_pole_of_lDim_point_ge_two P (lDim_point_ge_two_of_chi_eq hχ)

end Jacobians

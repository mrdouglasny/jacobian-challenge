/-
  Riemann–Roch INTERFACE (the meet-in-the-middle).

  Goal: reduce the headline consumer `exists_singleSimplePole_of_genus_zero` to ONE genuine
  classical input — Riemann–Roch — by PROVING every step in between (no typeclass
  relocation). When the Dolbeault→Serre climb (G2–G4) discharges that single input, the
  headline theorem falls out.

  PROVEN (axiom-clean): the ℂ-module on `MeromorphicFunction X` (so `L(D)` can be a
  `Submodule ℂ`); `linearSystem D` as a `Submodule` + `lDim`.

  ISOLATED INPUTS (the genuine wall — the only remaining gaps here):
    • `exists_riemannRoch_divisor` — a canonical divisor `K` with `l(D)−l(K−D)=deg D+1−g`
      (Forster 16.9; ⟸ Dolbeault/Serre, absent from Mathlib).
    • `MeromorphicFunction.deg_div` — every principal divisor has degree 0 (residue theorem).

  REAL REDUCTIONS STILL TO PROVE (no theater — these are genuine, not relocations):
  faithfulness/identity theorem (nonzero ⟹ order ≠ ⊤), `l(0)=1` via Liouville, `l(D)=0` for
  `deg D<0`, and the single-simple-pole extraction.
-/
import Jacobians.Abel
import Jacobians.LinearSystem
import Jacobians.MeromorphicLiouville
import Jacobians.DegDivResidue
import Jacobians.ProperMapDegreeSheets
import Jacobians.Dolbeault.DolbeaultLadder
import Jacobians.Dolbeault.LerayCoverExists
import Jacobians.Dolbeault.SkyscraperProductWitness

-- Many declarations here are purely algebraic (the ℂ-module on `MeromorphicFunction`) and use
-- only `[ChartedSpace ℂ X]`, not the full compact-manifold hypotheses carried by the consumers.
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]


/-- **Riemann–Roch** (Forster Thm 16.9, Serre-dual form): a canonical divisor `K` with
`l(D) − l(K−D) = deg D + 1 − g` for every `D`.

**Now CONNECTED to its proof** (it was previously a standalone unproved obligation duplicating, but
disconnected from, the ladder that proves it — the `CechSection → RiemannRoch` import cycle, broken
by extracting `LinearSystem`). It is the PROVEN ladder composition
`DolbeaultLadder.riemannRoch_equality_of_ladder`
(cohomological RR + the `h⁰=l` bridge + Serre at `0`/general), instantiated at a Leray cover supplied
by `LerayCoverExists.exists_lerayCover`. So discharging this is now exactly: the ladder leaves
(`arithmeticGenus_eq_genus`, `serre_h1_eq`, `cohomological_riemannRoch`/`exists_skyscraperLES`,
`h0Dim_eq_lDim`/`cechRestrictL_surjective`, finiteness) **plus** the one good-cover geometric input
`hOverlaps` below — no separate opaque RR obligation.

The Leray cover is supplied **UNCONDITIONALLY** by `exists_lerayCover` (STEP 2a, done): `IsLeray` was
weakened to its first conjunct alone (acyclic SETS), which for `H¹` is all Cartan's comparison
`0 → Ȟ¹(𝔘,𝒪) → H¹(X,𝒪) → Ȟ⁰(𝔘,ℋ¹)` needs (overlap acyclicity is `H²`+ only; `GoodCover` proved the
conjunct unused). So there is NO good-cover `hOverlaps` gap; the only sorries beneath this are now the
genuine analytic ladder leaves. -/
theorem exists_riemannRoch_divisor :
    ∃ K : Divisor X, ∀ D : Divisor X,
      (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
        = Divisor.deg X D + 1 - (genus X : ℤ) := by
  -- A *realizable* Leray cover exists: the canonical chart-disk cover is both Leray (acyclic sets)
  -- and locally realizable (the product witness, `locallyRealizable_chartDiskCover`).
  obtain ⟨𝔘, hL, hR⟩ := Dolbeault.exists_realizableLerayCover (X := X)
  -- The RR equality on that cover is the PROVEN ladder composition (mod the ladder's named leaves).
  exact Dolbeault.riemannRoch_equality_of_ladder 𝔘 hL hR

/-- Every principal divisor has degree `0` (Forster Cor. 4.25 / the argument principle). **PROVEN**
via the **degree route**: `deg (div f) = zerosCount f − polesCount f` (`deg_div_eq_zeros_sub_poles`),
and both counts equal a common proper-map degree `d` (`ProperMapDegreeSheets.exists_properMapDegree_proven`,
the §17.9 conservation-of-number construction — now axiom-clean), so the difference is `0`. The RR
derivations below consume this `deg_div`. (The old standalone `DegDivResidue.exists_properMapDegree`
that approach is now superseded by this proven route and no longer on any critical path.) -/
theorem MeromorphicFunction.deg_div (f : MeromorphicFunction X) :
    Divisor.deg X f.div = 0 := by
  obtain ⟨d, hz, hp⟩ := Jacobians.ProperMapDegreeSheets.exists_properMapDegree_proven f
  rw [deg_div_eq_zeros_sub_poles, hz, hp, sub_self]

/-! ## Part 3: negative-degree vanishing (explicit finiteness, dim 0)

The first genuine consequence, proved outright from `deg_div` + faithfulness: a linear system of
negative degree is trivial. This is `FiniteDimensional` with `l(D) = 0`, the cleanest explicit
finiteness — and it uses *only* the residue-theorem input, not the general finiteness theorem. -/

/-- `l(D) = 0` when `deg D < 0`. Any `f ∈ L(D)` with nonzero germ would give (by faithfulness) a
divisor `div f ≥ −D` with `deg(div f) = 0 ≥ −deg D > 0`, impossible; so every `f ∈ L(D)` is germ-
zero, the quotient `L(D)/germZero` is trivial, and its dimension is `0`. -/
theorem lDim_eq_zero_of_deg_neg (D : Divisor X) (hD : Divisor.deg X D < 0) :
    lDim (X := X) D = 0 := by
  have hsub : linearSystem (X := X) D ≤ germZeroSubmodule := by
    intro f hf
    by_contra hng
    have hex : ∃ x₀, f.orderW x₀ ≠ ⊤ := by
      by_contra h; push_neg at h; exact hng h
    have hfaith : ∀ z : X, f.orderW z ≠ ⊤ := fun z =>
      MeromorphicFunction.orderW_ne_top_of_exists f hex z
    have hdiv : ∀ x, -(D x) ≤ (f.div : Divisor X) x := by
      intro x
      have hmem : (-(D x) : WithTop ℤ) ≤ f.orderW x := hf x
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfaith x)
      rw [← hn] at hmem
      have hdivx : (f.div : Divisor X) x = n := by
        show (f.orderW x).untop₀ = n
        rw [← hn]; rfl
      rw [hdivx]; exact WithTop.coe_le_coe.mp hmem
    have heff : ∀ x, 0 ≤ (f.div + D) x := fun x => by
      rw [Finsupp.add_apply]; linarith [hdiv x]
    have hdeg_eff : (0 : ℤ) ≤ Divisor.deg X (f.div + D) := by
      change (0 : ℤ) ≤ ∑ i ∈ (f.div + D).support, (f.div + D) i
      exact Finset.sum_nonneg fun i _ => heff i
    rw [map_add, MeromorphicFunction.deg_div f] at hdeg_eff
    omega
  rw [lDim]
  have htop : (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) D) = ⊤ :=
    Submodule.comap_subtype_eq_top.mpr hsub
  rw [htop]
  haveI : Subsingleton (↥(linearSystem (X := X) D) ⧸
      (⊤ : Submodule ℂ ↥(linearSystem (X := X) D))) :=
    ⟨fun a b => Quotient.inductionOn₂' a b fun x y =>
      (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top⟩
  exact Module.finrank_zero_of_subsingleton


/-! ## Part 4: standard RR consequences (pure arithmetic from RR + `l(0)=1`) -/

/-- `l(K) = g`, from Riemann–Roch at `D = 0` (and `l(0) = 1`). -/
theorem lDim_canonical_eq_genus {K : Divisor X}
    (hrr : ∀ D : Divisor X, (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
      = Divisor.deg X D + 1 - (genus X : ℤ)) : lDim (X := X) K = genus X := by
  have h := hrr 0
  rw [sub_zero, Divisor.deg_zero, lDim_zero_eq_one] at h
  omega

/-- `deg K = 2g − 2`, from Riemann–Roch at `D = K`. -/
theorem deg_canonical {K : Divisor X}
    (hrr : ∀ D : Divisor X, (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
      = Divisor.deg X D + 1 - (genus X : ℤ)) : Divisor.deg X K = 2 * (genus X : ℤ) - 2 := by
  have h := hrr K
  rw [sub_self, lDim_zero_eq_one, lDim_canonical_eq_genus hrr] at h
  omega

/-! ## Part 5: the meet-in-the-middle — discharge the consumer from RR -/

/-- **Touch point.** `genus X = 0` + Riemann–Roch ⟹ a meromorphic function with a single simple
pole. RR at `D = P` gives `l(P) = 2 > 1 = l(0)`, so `L(P)/germZero` is not spanned by the constant
class; a member outside that span is not germ-constant, hence (by Liouville's contrapositive
`germ_eq_const_of_mem_linearSystem_zero`) has a pole, necessarily a *simple* pole at `P` — the only
pole `L(P)` permits — and by faithfulness its order is finite everywhere. This discharges
`exists_singleSimplePole_of_genus_zero` modulo `{riemannRoch, deg_div}`. -/
theorem exists_singleSimplePole_of_genus_zero_of_rr (hg : genus X = 0) :
    ∃ (P : X) (f : MeromorphicFunction X), f.HasSingleSimplePole P := by
  obtain ⟨P⟩ := (inferInstance : Nonempty X)
  obtain ⟨K, hrr⟩ := exists_riemannRoch_divisor (X := X)
  refine ⟨P, ?_⟩
  set DP : Divisor X := Finsupp.single P 1 with hDP
  have hdegDP : Divisor.deg X DP = 1 := by rw [hDP, Divisor.deg_single]
  -- `l(P) = 2`.
  have hlKDP : lDim (X := X) (K - DP) = 0 := by
    apply lDim_eq_zero_of_deg_neg
    rw [Divisor.deg_sub, deg_canonical hrr, hdegDP, hg]; norm_num
  have hlDP : lDim (X := X) DP = 2 := by
    have h := hrr DP; rw [hlKDP, hdegDP, hg] at h; omega
  -- The constant `1` as a member of `L(P)`, with order `0`.
  have h1m : IsMeromorphic X (fun _ : X => (1 : ℂ)) := fun x => MeromorphicAt.const 1 _
  have horder1 : ∀ x, (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X).orderW x = 0 := by
    intro x
    show meromorphicOrderAt ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) _ = 0
    rw [show ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) = (fun _ => (1 : ℂ)) from rfl,
      meromorphicOrderAt_const]; simp
  have hmem1 : (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) ∈ linearSystem (X := X) DP := by
    intro x; rw [horder1 x]
    have hge : (0 : ℤ) ≤ DP x := by
      classical rw [hDP, Finsupp.single_apply]; split <;> norm_num
    exact_mod_cast neg_nonpos.mpr hge
  set q1 : ↥(linearSystem (X := X) DP) := ⟨⟨fun _ => 1, h1m⟩, hmem1⟩ with hq1
  -- Work in the quotient `Q := L(P)/germZero`, of dimension `l(P) = 2`; pin its submodule once.
  set c1 : ↥(linearSystem (X := X) DP) ⧸
      (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) DP) :=
    Submodule.Quotient.mk q1 with hc1
  have hfr : Module.finrank ℂ (↥(linearSystem (X := X) DP) ⧸
      (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) DP)) = 2 := hlDP
  -- `[1] ≠ 0`, so `span {[1]}` has dimension 1 < 2 = `l(P)`, hence is not all of `L(P)/germZero`.
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
    exact absurd h1 (by norm_num)
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
    have hge : (0 : WithTop ℤ) ≤ (f : MeromorphicFunction X).orderW x₀ := by simpa using hmemf
    exact absurd (lt_of_le_of_lt hge hx₀) (lt_irrefl _)
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

end Jacobians

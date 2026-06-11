/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerreUnwind
import KirovDolbeault.Dolbeault.FineResidue.DescentVanish

/-!
# §17.7 unwinding, detection form — the reduction of `UnwindRegularity` to a detecting class

`GlobalResidue.UnwindRegularity G D` (`SerreUnwind.lean`) demands: a level-`E` functional
`ι_E(v)` factoring through `H¹(𝒪_E) → H¹(𝒪_D)` forces `v ∈ L(K−D)`.  Contrapositively it is a
**detection** statement: for `v ∉ L(K−D)` there must be a test class `ξ ∈ ker(H¹(𝒪_E) → H¹(𝒪_D))`
with `ι_E(v)(ξ) ≠ 0` — then no factoring `lam` can exist (`lam` kills `incl ξ = 0` while the
pairing does not).  This file proves that reduction (`unwindRegularity_of_detects`, pure linear
algebra, valid for ANY `GlobalResidue`), plus the order bookkeeping locating the **forced bad
point** (`docs/planning/UNWIND_ROUTE.md`):

* `orderW_eq_of_sub_germZero` — germ-zero junk does not move `orderW`, so membership in
  `L(K−D)` is a property of the `lSysModule` class.
* `exists_lSysInclMono_eq_iff` — `mk f` is in the image of `L(K−D) → L(K−E)` iff `f` itself
  satisfies the `L(K−D)` order bounds.
* `exists_bad_point` — a class outside the image has a point `b` with FINITE order `n` and
  `E b − K b ≤ n < D b − K b`; in particular `E b < D b` (bad points are jump points).

The detecting class itself (the analytic half: the skyscraper test cocycle and its residue
evaluation through the R-lane engine) is built downstream for the concrete fine-sheaf residue.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), Lemma 17.7 (p. 137).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Module

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 0 — germ-zero junk does not move `orderW` -/

/-- `min`-bound for the order of a sum of meromorphic functions (the `linearSystem.add_mem'`
computation, exported). -/
theorem MeromorphicFunction.min_orderW_le_add (f g : MeromorphicFunction X) (x : X) :
    min (f.orderW x) (g.orderW x) ≤ (f + g).orderW x :=
  meromorphicOrderAt_add (f.meromorphic x) (g.meromorphic x)

/-- **Germ-zero differences do not move `orderW`**: if `f − f'` is a germ-zero junk function
(order `⊤` everywhere), then `f` and `f'` have the same order at every point. -/
theorem MeromorphicFunction.orderW_eq_of_sub_germZero {f f' : MeromorphicFunction X}
    (hd : f - f' ∈ germZeroSubmodule (X := X)) (x : X) :
    f.orderW x = f'.orderW x := by
  have hd' : f' - f ∈ germZeroSubmodule (X := X) := by
    have := neg_mem hd
    rwa [neg_sub] at this
  refine le_antisymm ?_ ?_
  · -- `f' = (f' − f) + f`, and the junk summand has order `⊤`
    have h1 := MeromorphicFunction.min_orderW_le_add (f' - f) f x
    rw [sub_add_cancel] at h1
    rw [hd' x, min_eq_right le_top] at h1
    exact h1
  · -- `f = (f − f') + f'`
    have h1 := MeromorphicFunction.min_orderW_le_add (f - f') f' x
    rw [sub_add_cancel] at h1
    rw [hd x, min_eq_right le_top] at h1
    exact h1

/-! ## Part 1 — the image of the monotone linear-system inclusion, order-theoretically -/

namespace Dolbeault

variable {K : Divisor X}

/-- **Image characterization of `lSysInclMono`**: the class of `f ∈ L(K−E)` lies in the image
of `L(K−D) → L(K−E)` (`E ≤ D`) iff `f` itself satisfies the `L(K−D)` order bounds.  (Junk-free:
germ-zero representatives have identical orders.) -/
theorem exists_lSysInclMono_eq_iff {E D : Divisor X} (hED : ∀ x, E x ≤ D x)
    (f : ↥(linearSystem (X := X) (K - E))) :
    (∃ u : lSysModule (X := X) (K - D),
        lSysInclMono (divisor_sub_le_sub_left K hED) u = Submodule.Quotient.mk f)
      ↔ (f : MeromorphicFunction X) ∈ linearSystem (X := X) (K - D) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨u₀, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [lSysInclMono_mk] at hu
    -- the difference of representatives is germ-zero
    have hdiff := (Submodule.Quotient.eq _).mp hu
    rw [Submodule.submoduleOf, Submodule.mem_comap] at hdiff
    have hdiff' : (u₀ : MeromorphicFunction X) - (f : MeromorphicFunction X)
        ∈ germZeroSubmodule (X := X) := hdiff
    intro x
    rw [← MeromorphicFunction.orderW_eq_of_sub_germZero hdiff' x]
    exact u₀.2 x
  · intro hf
    refine ⟨Submodule.Quotient.mk ⟨(f : MeromorphicFunction X), hf⟩, ?_⟩
    rw [lSysInclMono_mk]
    exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- **The forced bad point** (Forster 17.7's evaluation point): a level-`E` class outside the
image of `L(K−D)` has a point `b` where the order is FINITE, at least the `L(K−E)` bound, and
strictly below the `L(K−D)` bound.  In particular `E b < D b`: bad points are jump points of
`E ≤ D`. -/
theorem exists_bad_point {E D : Divisor X} (hED : ∀ x, E x ≤ D x)
    (f : ↥(linearSystem (X := X) (K - E)))
    (hno : ¬ ∃ u : lSysModule (X := X) (K - D),
        lSysInclMono (divisor_sub_le_sub_left K hED) u = Submodule.Quotient.mk f) :
    ∃ (b : X) (n : ℤ), (f : MeromorphicFunction X).orderW b = (n : WithTop ℤ) ∧
      E b - K b ≤ n ∧ n < D b - K b := by
  rw [exists_lSysInclMono_eq_iff hED f] at hno
  simp only [linearSystem, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, not_forall] at hno
  obtain ⟨b, hb⟩ := hno
  -- the failed bound: `ord < D b − K b` (note `−((K−D) b) = D b − K b`)
  have hKD : (-((K - D : Divisor X) b) : ℤ) = D b - K b := by
    rw [Finsupp.sub_apply]
    ring
  have hKE : (-((K - E : Divisor X) b) : ℤ) = E b - K b := by
    rw [Finsupp.sub_apply]
    ring
  have hlt : (f : MeromorphicFunction X).orderW b < ((D b - K b : ℤ) : WithTop ℤ) := by
    rw [← hKD]
    exact lt_of_not_ge hb
  have hge : ((E b - K b : ℤ) : WithTop ℤ) ≤ (f : MeromorphicFunction X).orderW b := by
    rw [← hKE]
    exact f.2 b
  -- the order is finite
  have hne : (f : MeromorphicFunction X).orderW b ≠ ⊤ := by
    intro hc
    rw [hc] at hlt
    exact (not_top_lt hlt)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨b, n, hn.symm, ?_, ?_⟩
  · rw [← hn] at hge
    exact_mod_cast hge
  · rw [← hn] at hlt
    exact_mod_cast hlt

/-! ## Part 2 — the detection reduction (pure linear algebra, any `GlobalResidue`) -/

namespace GlobalResidue

variable {𝔘 : FiniteCover X}

/-- **The detection reduction of Forster 17.7**: if every class outside the image of
`L(K−D) → L(K−E)` is DETECTED by some kernel class of `H¹(𝒪_E) → H¹(𝒪_D)` (nonzero pairing),
then `UnwindRegularity G D` holds.  A factoring `lam` would have to kill the detector
(`lam (incl ξ) = lam 0 = 0`) while the pairing does not — contradiction. -/
theorem unwindRegularity_of_detects (G : GlobalResidue 𝔘 K) (D : Divisor X)
    (hdet : ∀ (E : Divisor X) (hED : ∀ x, E x ≤ D x) (v : lSysModule (X := X) (K - E)),
      ¬ (∃ u : lSysModule (X := X) (K - D),
          lSysInclMono (divisor_sub_le_sub_left K hED) u = v) →
      ∃ ξ : 𝔘.cechH1 E, 𝔘.h1InclMono hED ξ = 0 ∧ (G.pairing E v) ξ ≠ 0) :
    G.UnwindRegularity D := by
  intro E hED v lam hfac
  by_contra hno
  obtain ⟨ξ, hker, hne⟩ := hdet E hED v hno
  apply hne
  have h1 := DFunLike.congr_fun hfac ξ
  rw [h1, LinearMap.comp_apply, hker, map_zero]

end GlobalResidue

/-! ## Part 3 — the skyscraper test cocycle at an isolated jump point

The detecting class for the concrete fine-sheaf residue: at an isolated jump point `b` with
level `E b ≤ m < D b`, the **exact-order local Mittag–Leffler witness** (proven for the
canonical chart-disk cover, `exists_orderExact_witness_chartDisk`) supplies a section
`γ ∈ 𝒪_{Ě+b}(U j₀)` (`Ě := E + (m − E b)·b`) of order exactly `−(m+1)` at `b`.  Its
`Pi.single` coboundary is a `Z¹(𝒪_E)` cocycle (overlaps avoid `b` by isolation, and the
`𝒪_{Ě+b}` bound IS the `𝒪_E` bound off `b` — the witness absorbs all `E`-negative zero
requirements), trivialized at level `D` by the cochain itself (`m + 1 ≤ D b`). -/

/-- Pointwise-monotone divisor comparison on an open: `𝒪_{D₁}(V) ≤ 𝒪_{D₂}(V)`. -/
theorem OmegaD_mono {D₁ D₂ : Divisor X} {V : Opens X} (h : ∀ x ∈ V, D₁ x ≤ D₂ x) :
    OmegaD (X := X) D₁ V ≤ OmegaD D₂ V := by
  rintro f ⟨hmer, hord⟩
  refine ⟨hmer, fun v => le_trans ?_ (hord v)⟩
  have e1 : (-(D₁ v.1) : WithTop ℤ) = ((-(D₁ v.1) : ℤ) : WithTop ℤ) := rfl
  have e2 : (-(D₂ v.1) : WithTop ℤ) = ((-(D₂ v.1) : ℤ) : WithTop ℤ) := rfl
  rw [e1, e2]
  exact_mod_cast neg_le_neg (h v.1 v.2)

/-- Germ-class version of `OmegaD_mono`. -/
theorem OmegaDGerm_mono {D₁ D₂ : Divisor X} {V : Opens X} (h : ∀ x ∈ V, D₁ x ≤ D₂ x) :
    OmegaDGerm (X := X) D₁ V ≤ OmegaDGerm D₂ V :=
  Submodule.map_mono (OmegaD_mono h)

/-- **The exact-order local Mittag–Leffler witness** on a chart-disk cover: at every cover set
`U j ∋ P` and divisor `D`, a section of `𝒪_{D+P}(U j)` of order EXACTLY `−D(P)−1` at `P`.
Strictly stronger than `LocallyRealizable` (which only asks for the top coefficient); proven
for the canonical cover by the factorized-rational product witness. -/
def ExactOrderWitness (𝔇 : ChartDiskCover X) : Prop :=
  ∀ (D : Divisor X) (j : 𝔇.toFiniteCover.ι) (P : X) (hP : P ∈ 𝔇.U j),
    ∃ γ : ↥(𝔇.U j) → ℂ, γ ∈ OmegaD (D + Finsupp.single P 1) (𝔇.U j) ∧
      ordU γ ⟨P, hP⟩ = ((-(D P) - 1 : ℤ) : WithTop ℤ)

/-- The canonical chart-disk cover has the exact-order witness
(`exists_orderExact_witness_chartDisk`, the factorized-rational product witness). -/
theorem exactOrderWitness_chartDiskCover [Nonempty X] :
    ExactOrderWitness (chartDiskCover (X := X)) := by
  intro D j P hP
  obtain ⟨γ, hmem, hord⟩ := exists_orderExact_witness_chartDisk D j P hP
  exact ⟨γ, hmem, hord⟩

section TestCocycle

variable {𝔇 : ChartDiskCover X} [DecidableEq 𝔇.toFiniteCover.ι]

/-- **The skyscraper test datum** at level `(E, b, m)`: a distinguished-chart section with pole
of order exactly `m+1` at `b` and the `𝒪_E` bounds everywhere else on `U j₀`
(`Ě := E + (m − E b)·b`, so `𝒪_{Ě + b}` is exactly that bound package). -/
structure TestCocycleData (𝔇 : ChartDiskCover X) (E : Divisor X) (j₀ : 𝔇.toFiniteCover.ι)
    (b : X) (hb : b ∈ (𝔇.U j₀ : Set X)) (m : ℤ) where
  /-- The distinguished-chart section. -/
  γ : ↥(𝔇.U j₀) → ℂ
  /-- `γ ∈ 𝒪_{Ě + b}(U j₀)` with `Ě := E + (m − E b)·b`. -/
  mem : γ ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j₀)
  /-- The order at `b` is exactly `−(m+1)`. -/
  ord : ordU γ ⟨b, hb⟩ = ((-m - 1 : ℤ) : WithTop ℤ)

/-- The exact-order witness inhabits the test datum at every admissible level (`E b ≤ m`). -/
theorem TestCocycleData.exists_of_witness (hwit : ExactOrderWitness 𝔇) {E : Divisor X}
    {j₀ : 𝔇.toFiniteCover.ι} {b : X} (hb : b ∈ (𝔇.U j₀ : Set X)) {m : ℤ} (hmE : E b ≤ m) :
    Nonempty (TestCocycleData 𝔇 E j₀ b hb m) := by
  obtain ⟨γ, hmem, hord⟩ := hwit (E + Finsupp.single b (m - E b)) j₀ b hb
  refine ⟨⟨γ, hmem, ?_⟩⟩
  rw [hord]
  congr 1
  have hEb : (E + Finsupp.single b (m - E b)) b = m := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
    ring
  rw [hEb]

namespace TestCocycleData

variable {E D : Divisor X} {j₀ : 𝔇.toFiniteCover.ι} {b : X} {hb : b ∈ (𝔇.U j₀ : Set X)} {m : ℤ}

/-- The divisor bound carried by the test section, at the marked point. -/
private theorem divisor_apply_self :
    (E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) b = m + 1 := by
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_same]
  ring

/-- The divisor bound carried by the test section, away from the marked point. -/
private theorem divisor_apply_ne {x : X} (hx : x ≠ b) :
    (E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) x = E x := by
  rw [Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (a := b) (a' := x) hx,
    Finsupp.single_eq_of_ne (a := b) (a' := x) hx]
  ring

/-- The skyscraper test 0-cochain: the test germ on the distinguished set, `0` elsewhere. -/
noncomputable def cochain (td : TestCocycleData 𝔇 E j₀ b hb m) :
    𝔇.toFiniteCover.toFiniteFamily.Cochain0 :=
  Pi.single j₀ (toGerm (𝔇.U j₀) td.γ)

theorem cochain_self (td : TestCocycleData 𝔇 E j₀ b hb m) :
    td.cochain j₀ = toGerm (𝔇.U j₀) td.γ := by
  rw [cochain, Pi.single_eq_same]

theorem cochain_of_ne (td : TestCocycleData 𝔇 E j₀ b hb m) {j : 𝔇.toFiniteCover.ι}
    (hj : j ≠ j₀) : td.cochain j = 0 := by
  rw [cochain, Pi.single_eq_of_ne hj]

/-- **Level-`D` membership of the test cochain** (`m + 1 ≤ D b`, `E ≤ D`): the cochain whose
coboundary trivializes the test class in `H¹(𝒪_D)`. -/
theorem cochain_mem_sections0 (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hED : ∀ x, E x ≤ D x) (hmD : m + 1 ≤ D b) :
    td.cochain ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 D := by
  intro i
  by_cases hi : i = j₀
  · rw [hi, td.cochain_self]
    refine OmegaDGerm_mono (D₁ := E + Finsupp.single b (m - E b) + Finsupp.single b 1)
      (fun x _ => ?_) ⟨td.γ, td.mem, rfl⟩
    by_cases hx : x = b
    · rw [hx, divisor_apply_self]
      exact hmD
    · rw [divisor_apply_ne hx]
      exact hED x
  · rw [td.cochain_of_ne hi]
    exact Submodule.zero_mem _

/-- **Level-`E` membership of the test coboundary**: the overlap components avoid `b`
(isolation), where the `𝒪_{Ě+b}` bound is the `𝒪_E` bound. -/
theorem delta_mem_sections1 (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hbiso : FineResidue.MLIsolated 𝔇 j₀ b) :
    𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain
      ∈ 𝔇.toFiniteCover.toFiniteFamily.sections1 E := by
  intro p
  obtain ⟨i, j⟩ := p
  have hδ : 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain (i, j)
      = rawRestrictG inf_le_right (td.cochain j) - rawRestrictG inf_le_left (td.cochain i) := by
    simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
  rw [hδ]
  by_cases hi : i = j₀ <;> by_cases hj : j = j₀
  · -- diagonal pair: the two restrictions agree (proof-irrelevant `≤`)
    rw [hi, hj]
    have heq : rawRestrictG (inf_le_right : (𝔇.U j₀ ⊓ 𝔇.U j₀ : Opens X) ≤ 𝔇.U j₀)
          (td.cochain j₀)
        = rawRestrictG (inf_le_left : (𝔇.U j₀ ⊓ 𝔇.U j₀ : Opens X) ≤ 𝔇.U j₀)
          (td.cochain j₀) := rfl
    rw [heq, sub_self]
    exact Submodule.zero_mem _
  · -- `i = j₀`, `j ≠ j₀`: the `−γ` side on an overlap avoiding `b`
    rw [hi, td.cochain_of_ne hj, map_zero, zero_sub]
    refine neg_mem ?_
    have h1 : rawRestrictG (inf_le_left : (𝔇.U j₀ ⊓ 𝔇.U j : Opens X) ≤ 𝔇.U j₀)
        (td.cochain j₀) ∈ OmegaDGerm
          (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j₀ ⊓ 𝔇.U j) := by
      rw [td.cochain_self]
      exact rawRestrictG_omegaDGerm _ ⟨td.γ, td.mem, rfl⟩
    refine OmegaDGerm_mono (fun x hx => ?_) h1
    have hxb : x ≠ b := fun hc => hbiso.2 j hj (hc ▸ hx.2)
    rw [divisor_apply_ne hxb]
  · -- `i ≠ j₀`, `j = j₀`: the `+γ` side
    rw [hj, td.cochain_of_ne hi, map_zero, sub_zero]
    have h1 : rawRestrictG (inf_le_right : (𝔇.U i ⊓ 𝔇.U j₀ : Opens X) ≤ 𝔇.U j₀)
        (td.cochain j₀) ∈ OmegaDGerm
          (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U i ⊓ 𝔇.U j₀) := by
      rw [td.cochain_self]
      exact rawRestrictG_omegaDGerm _ ⟨td.γ, td.mem, rfl⟩
    refine OmegaDGerm_mono (fun x hx => ?_) h1
    have hxb : x ≠ b := fun hc => hbiso.2 i hi (hc ▸ hx.1)
    rw [divisor_apply_ne hxb]
  · -- neither distinguished: `0 − 0`
    rw [td.cochain_of_ne hi, td.cochain_of_ne hj, map_zero, map_zero, sub_zero]
    exact Submodule.zero_mem _

/-- The test coboundary is a cocycle (`δ² = 0`). -/
theorem delta_mem_ker (td : TestCocycleData 𝔇 E j₀ b hb m) :
    𝔇.toFiniteCover.toFiniteFamily.cechDelta1
      (𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain) = 0 := by
  have h := DFunLike.congr_fun
    (𝔇.toFiniteCover.toFiniteFamily.cechDelta1_comp_cechDelta0) td.cochain
  rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h

/-- **The test cocycle**, as an element of `Z¹(𝒪_E)`. -/
noncomputable def cocycle (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hbiso : FineResidue.MLIsolated 𝔇 j₀ b) :
    ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 E) :=
  ⟨𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain,
    Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr td.delta_mem_ker, td.delta_mem_sections1 hbiso⟩⟩

@[simp] theorem cocycle_coe (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hbiso : FineResidue.MLIsolated 𝔇 j₀ b) :
    (td.cocycle hbiso : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain := rfl

/-- **The test class dies in `H¹(𝒪_D)`**: the monotone inclusion sends it to the class of a
`B¹(𝒪_D)`-coboundary. -/
theorem h1InclMono_cocycle_eq_zero (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hbiso : FineResidue.MLIsolated 𝔇 j₀ b) (hED : ∀ x, E x ≤ D x) (hmD : m + 1 ≤ D b) :
    𝔇.toFiniteCover.h1InclMono hED
      (Submodule.Quotient.mk (td.cocycle hbiso)) = 0 := by
  rw [𝔇.toFiniteCover.h1InclMono_mk, Submodule.Quotient.mk_eq_zero]
  rw [Submodule.submoduleOf, Submodule.mem_comap]
  exact ⟨td.cochain, td.cochain_mem_sections0 hED hmD, rfl⟩

end TestCocycleData

end TestCocycle

end Dolbeault

end Jacobians

end

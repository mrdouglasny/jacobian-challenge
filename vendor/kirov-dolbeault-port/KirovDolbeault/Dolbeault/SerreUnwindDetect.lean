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

end Dolbeault

end Jacobians

end

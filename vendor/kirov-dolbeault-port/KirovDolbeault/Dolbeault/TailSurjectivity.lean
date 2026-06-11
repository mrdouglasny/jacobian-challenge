/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailSerre
import KirovDolbeault.Dolbeault.SerreDuality
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRealCover

/-!
# The surjectivity half of tail Serre duality (Miranda VI.3.10) — tail tower T7

Over the T1–T6 substrate (`TailSerre.lean`, route `docs/planning/TAILRR_ROUTE.md`): for every
tail pair frame `P` and every divisor `D`, the residue pairing
`pairingL D : L(K−D)/junk →ₗ Dual(H¹_t(D))` is SURJECTIVE — discharging the named residual
input `P.PairingSurjective` of `tailRiemannRoch_of_pairingSurjective`, so that
`TailRiemannRoch X` now rests on frame existence (`Nonempty (TailPairFrame X)`) alone.

The proof is Miranda's recovery + growth pigeonhole, executed in pure Laurent-coefficient
algebra:

* Part A — the **general window product law** `planarCoeff_mul_window`
  (`c_m(A·B) = ∑_{k ∈ [lo,hi)} c_k(A)·c_{m−k}(B)` for `ord B ≥ m+1−hi`), derived from the
  proven residue case `resCoeff_mul_window` by the monomial shift, and the monomial
  coefficient spectrum `planarCoeff_zpow_self`.
* Part B — the X-level product law `coeffAt_mul_window`.
* Part C — the **multiplication–truncation operator** `mulTail f D : 𝒯 → 𝒯[D]`
  (`t ↦ trunc_D(f·t)` in coefficients), with: linearity in `f`, the upper kill
  (`f ∈ L(E)` sends `𝒰[D−E]` to `0`), the **transport identity**
  `mulTail f D (α_{D−E} g) = α_D (f·g)`, and the **local inverse tails**
  `invMonomialTail f p k lo hi` (the tail of `z^k/f` at `p`) with
  `mulTail f D (invMonomialTail …) = trunc_D(z^k at p)` — the division step, via the
  identity theorem `orderW_ne_top_of_exists` and `MeromorphicAt.inv`.
* Part D — the descended multiplication `mulH1 : H¹_t(D−E) → H¹_t(D)` (surjective for
  `f ≠ 0`), and the `ψ`-action on functionals `tailPsiAct φ : L(E)/junk →ₗ Dual(H¹_t(D−E))`,
  injective for `φ ≠ 0` (Miranda's Lemma VI.3.8 analogue).
* Part E — the **unwind** (Miranda VI.3.7/VI.3.9 analogue): a pigeonhole witness
  `ψ·φ = pairingL_{D−E}(w)` with `ψ ≠ 0` yields `g := w·ψ⁻¹ ∈ L(K−D)` with
  `pairingL D (g) = φ`, all by evaluating both sides on the local inverse tails.
* Part F — the **headline**: `TailPairFrame.pairingSurjective` via
  `serre_surjectivity_dim_core` over the proven `tail_riemannRoch_I` arithmetic, and the
  unconditional-in-`PairingSurjective` upgrades `TailPairFrame.tailRiemannRoch_of_frame`,
  `h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame'`.

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI §3,
Proposition 3.10 and Lemmas 3.6–3.9; Forster (GTM 81) §17.9 for the count.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Filter Module

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians

namespace Dolbeault

/-! ## Part A — planar supplements: the monomial spectrum and the general window law -/

variable {F G A B : ℂ → ℂ} {c : ℂ}

/-- **The monomial coefficient spectrum**: `c_m((z−c)^k) = δ_{mk}` at every order `m`. -/
theorem planarCoeff_zpow_self (m k : ℤ) (c : ℂ) :
    planarCoeff m (fun z => (z - c) ^ k) c = if m = k then 1 else 0 := by
  have hmer : MeromorphicAt (fun z => (z - c) ^ k) c := meromorphicAt_zpow_self c k
  have hord : meromorphicOrderAt (fun z => (z - c) ^ k) c = (k : WithTop ℤ) :=
    meromorphicOrderAt_zpow_self k c
  rcases lt_trichotomy m k with hmk | rfl | hmk
  · rw [if_neg (by omega)]
    refine planarCoeff_eq_zero_of_lt_order ?_ hmer
    rw [hord]
    exact_mod_cast hmk
  · rw [if_pos rfl, planarCoeff_eq_fullCoeffFrom hmer (le_of_eq hord.symm) le_rfl,
      sub_self, Int.toNat_zero, fullCoeffFrom_offset_zero', laurentCoeff_zpow_self]
  · -- above the top: every strip beyond the leading term is the zero function
    have hstrip : ∀ j : ℕ, stripFun (fun z => (z - c) ^ k) c k (j + 1) = fun _ => (0 : ℂ) := by
      intro j
      induction j with
      | zero =>
        funext z
        rw [stripFun_succ]
        show stripFun (fun z => (z - c) ^ k) c k 0 z
            - laurentCoeff (k + (0 : ℕ)) (stripFun (fun z => (z - c) ^ k) c k 0) c
              * (z - c) ^ (k + (0 : ℕ)) = 0
        rw [stripFun_zero_iter]
        push_cast
        rw [add_zero, laurentCoeff_zpow_self]
        ring
      | succ j ih =>
        funext z
        rw [stripFun_succ, ih]
        show (0 : ℂ) - laurentCoeff (k + (j + 1 : ℕ)) (fun _ => (0 : ℂ)) c
            * (z - c) ^ (k + (j + 1 : ℕ)) = 0
        rw [show (fun _ => (0 : ℂ)) = (0 : ℂ → ℂ) from rfl, laurentCoeff_zero_fun]
        ring
    rw [if_neg (by omega), planarCoeff_eq_fullCoeffFrom hmer (le_of_eq hord.symm) (by omega)]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (m - k).toNat = j + 1 :=
      ⟨(m - k).toNat - 1, by omega⟩
    rw [hj, fullCoeffFrom, hstrip j,
      show (fun _ => (0 : ℂ)) = (0 : ℂ → ℂ) from rfl, laurentCoeff_zero_fun]

/-- **The general window product law** (`resCoeff_mul_window` at every order `m`): the
order-`m` coefficient of a product reads the window coefficients of `A` against the shifted
coefficients of `B`, provided `B`'s order clears the window top (`ord B ≥ m + 1 − hi`). -/
theorem planarCoeff_mul_window (hA : MeromorphicAt A c) (hB : MeromorphicAt B c)
    {lo hi m : ℤ} (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt A c) (hlohi : lo ≤ hi)
    (hBord : ((m + 1 - hi : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt B c) :
    planarCoeff m (fun z => A z * B z) c
      = ∑ k ∈ Finset.Ico lo hi, planarCoeff k A c * planarCoeff (m - k) B c := by
  -- shift `B` by `(z−c)^{−1−m}` and apply the residue case
  set B' : ℂ → ℂ := fun z => (z - c) ^ (-1 - m) * B z with hB'def
  have hB' : MeromorphicAt B' c := (meromorphicAt_zpow_self c (-1 - m)).mul hB
  have hB'ord : ((-hi : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt B' c := by
    have hmul : meromorphicOrderAt B' c
        = ((-1 - m : ℤ) : WithTop ℤ) + meromorphicOrderAt B c := by
      rw [hB'def, show (fun z => (z - c) ^ (-1 - m) * B z)
          = (fun z => (z - c) ^ (-1 - m)) * B from rfl,
        meromorphicOrderAt_mul (meromorphicAt_zpow_self c (-1 - m)) hB,
        meromorphicOrderAt_zpow_self]
    rw [hmul]
    calc ((-hi : ℤ) : WithTop ℤ)
        = ((-1 - m : ℤ) : WithTop ℤ) + ((m + 1 - hi : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
          ring
      _ ≤ ((-1 - m : ℤ) : WithTop ℤ) + meromorphicOrderAt B c :=
          add_le_add le_rfl hBord
  have hlaw := resCoeff_mul_window hA hB' hlo hlohi hB'ord
  -- LHS: `c_{−1}(A·B') = c_{−1}((z−c)^{−1−m}·(A·B)) = c_m(A·B)`
  have hL : planarCoeff (-1) (fun z => A z * B' z) c
      = planarCoeff m (fun z => A z * B z) c := by
    have hfun : (fun z => A z * B' z)
        = fun z => (z - c) ^ (-1 - m) * (A z * B z) := by
      funext z
      rw [hB'def]
      ring
    have h1 : planarCoeff (-1) (fun z => (z - c) ^ (-1 - m) * (A z * B z)) c
        = planarCoeff (-1 - (-1 - m)) (fun z => A z * B z) c :=
      planarCoeff_monomial_mul (-1 - m) (-1) (hA.mul hB)
    rw [hfun, h1, show (-1 - (-1 - m) : ℤ) = m from by ring]
  -- RHS: `c_{−1−k}(B') = c_{m−k}(B)` termwise
  have hR : ∀ k ∈ Finset.Ico lo hi,
      planarCoeff k A c * planarCoeff (-1 - k) B' c
        = planarCoeff k A c * planarCoeff (m - k) B c := by
    intro k _
    rw [hB'def, planarCoeff_monomial_mul (-1 - m) (-1 - k) hB,
      show (-1 - k - (-1 - m) : ℤ) = m - k from by ring]
  rw [← hL, hlaw]
  exact Finset.sum_congr rfl hR

/-- Level helper: `min(untop₀ o, x)` is a valid level below `o` for every `o : WithTop ℤ`. -/
theorem coe_min_untop₀_le_self (o : WithTop ℤ) (x : ℤ) :
    ((min o.untop₀ x : ℤ) : WithTop ℤ) ≤ o := by
  cases o with
  | top => exact le_top
  | coe n =>
    rw [WithTop.untop₀_coe]
    exact_mod_cast min_le_left n x

/-! ## Part B — the X-level product window law -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The X-level product window law** (window on the SECOND factor `g`): for `m` cleared by
`f`'s order (`ord_p f ≥ m + 1 − hi`),
`c_m(f·g) = ∑_{k ∈ [lo,hi)} c_k(g)·c_{m−k}(f)`. -/
theorem MeromorphicFunction.coeffAt_mul_window (f g : MeromorphicFunction X) (p : X)
    {lo hi m : ℤ} (hlo : (lo : WithTop ℤ) ≤ g.orderW p) (hlohi : lo ≤ hi)
    (hford : ((m + 1 - hi : ℤ) : WithTop ℤ) ≤ f.orderW p) :
    (f * g).coeffAt p m
      = ∑ k ∈ Finset.Ico lo hi, g.coeffAt p k * f.coeffAt p (m - k) := by
  classical
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set Af : ℂ → ℂ := f.toFun ∘ (chartAt (H := ℂ) p).symm with hAf
  set Ag : ℂ → ℂ := g.toFun ∘ (chartAt (H := ℂ) p).symm with hAg
  have hAfm : MeromorphicAt Af c := f.meromorphic p
  have hAgm : MeromorphicAt Ag c := g.meromorphic p
  have hlaw := planarCoeff_mul_window hAgm hAfm (m := m) hlo hlohi hford
  have hread : (f * g).coeffAt p m = planarCoeff m (fun z => Ag z * Af z) c := by
    show planarCoeff m ((f * g).toFun ∘ (chartAt (H := ℂ) p).symm) c
        = planarCoeff m (fun z => Ag z * Af z) c
    congr 1
    funext z
    show f.toFun ((chartAt (H := ℂ) p).symm z) * g.toFun ((chartAt (H := ℂ) p).symm z)
        = Ag z * Af z
    rw [hAf, hAg]
    show f.toFun ((chartAt (H := ℂ) p).symm z) * g.toFun ((chartAt (H := ℂ) p).symm z)
        = g.toFun ((chartAt (H := ℂ) p).symm z) * f.toFun ((chartAt (H := ℂ) p).symm z)
    ring
  rw [hread, hlaw]
  rfl

end Dolbeault

end Jacobians

end

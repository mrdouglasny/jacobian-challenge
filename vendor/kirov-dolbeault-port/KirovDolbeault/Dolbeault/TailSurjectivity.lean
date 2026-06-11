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

/-! ## Part C — the multiplication–truncation operator `mulTail` -/

/-- **The single-slot multiplication tail**: the `D`-truncated tail of `f·(z^k at p)` — the
window `[min(ord f + k, −D p), −D p)` of shifted full coefficients of `f`. -/
def mulTailSingle (f : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ) : GlobalTails X :=
  ∑ m ∈ Finset.Ico (min ((f.orderW q.1).untop₀ + q.2) (-(D q.1))) (-(D q.1)),
    Finsupp.single (q.1, m) (f.coeffAt q.1 (m - q.2))

/-- **The coefficient law of the single-slot tail**: the read at `(p', m)` is the shifted
coefficient `c_{m−k}(f)` strictly below the cut at `p`, `0` elsewhere. -/
theorem mulTailSingle_apply (f : MeromorphicFunction X) (D : Divisor X) (p : X) (k : ℤ)
    (p' : X) (m : ℤ) :
    mulTailSingle f D (p, k) (p', m)
      = if p' = p ∧ m < -(D p) then f.coeffAt p (m - k) else 0 := by
  classical
  rw [mulTailSingle, Finsupp.finsetSum_apply]
  rcases eq_or_ne p' p with rfl | hne
  · have hterm : ∀ m' ∈ Finset.Ico (min ((f.orderW (p', k).1).untop₀ + (p', k).2)
        (-(D (p', k).1))) (-(D (p', k).1)),
        (Finsupp.single ((p', k).1, m') (f.coeffAt (p', k).1 (m' - (p', k).2))) (p', m)
          = if m' = m then f.coeffAt p' (m - k) else 0 := by
      intro m' _
      rw [Finsupp.single_apply]
      simp only [Prod.mk.injEq, true_and]
      rcases eq_or_ne m' m with rfl | hm'
      · simp
      · rw [if_neg hm', if_neg hm']
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ m fun _ => f.coeffAt p' (m - k)]
    simp only [Finset.mem_Ico, true_and]
    by_cases hcut : m < -(D p')
    · rw [if_pos hcut]
      by_cases hbot : min ((f.orderW p').untop₀ + k) (-(D p')) ≤ m
      · rw [if_pos ⟨hbot, hcut⟩]
      · rw [if_neg (by omega)]
        have hk : m - k < (f.orderW p').untop₀ := by omega
        exact (MeromorphicFunction.coeffAt_eq_zero_of_lt_untop₀ hk).symm
    · rw [if_neg hcut, if_neg (by omega)]
  · rw [if_neg (by simp [hne])]
    refine Finset.sum_eq_zero fun m' _ => ?_
    rw [Finsupp.single_apply, if_neg]
    simp only [Prod.mk.injEq, not_and]
    exact fun h => absurd h.symm hne

/-- The single-slot tail lands strictly below the cut. -/
theorem mulTailSingle_mem_tailSpace (f : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ) :
    mulTailSingle f D q ∈ tailSpace D := by
  obtain ⟨p, k⟩ := q
  rw [mem_tailSpace_iff]
  intro q' hq'
  obtain ⟨p', m⟩ := q'
  rw [mulTailSingle_apply]
  rcases eq_or_ne p' p with rfl | hne
  · rw [if_neg (by simp only [true_and, not_lt]; exact hq')]
  · rw [if_neg (by simp [hne])]

/-- **The multiplication–truncation operator** `t ↦ trunc_D(f·t)`, in coefficients. -/
def mulTail (f : MeromorphicFunction X) (D : Divisor X) :
    GlobalTails X →ₗ[ℂ] GlobalTails X :=
  Finsupp.lsum ℂ fun q => LinearMap.toSpanSingleton ℂ (GlobalTails X) (mulTailSingle f D q)

@[simp] theorem mulTail_single (f : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ)
    (a : ℂ) : mulTail f D (Finsupp.single q a) = a • mulTailSingle f D q := by
  rw [mulTail, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

theorem mulTail_apply (f : MeromorphicFunction X) (D : Divisor X) (t : GlobalTails X) :
    mulTail f D t = t.sum fun q a => a • mulTailSingle f D q := by
  rw [mulTail, Finsupp.lsum_apply]
  exact Finsupp.sum_congr fun q _ => LinearMap.toSpanSingleton_apply ℂ _ _ _

/-- `mulTail` lands in `𝒯[D]`. -/
theorem mulTail_mem_tailSpace (f : MeromorphicFunction X) (D : Divisor X)
    (t : GlobalTails X) : mulTail f D t ∈ tailSpace D := by
  rw [mulTail_apply]
  refine Submodule.finsuppSum_mem _ _ _ _ fun q _ => ?_
  exact Submodule.smul_mem _ _ (mulTailSingle_mem_tailSpace f D q)

/-- **The point-tail evaluation** (the shared bookkeeping engine): `mulTail` of a
single-point coefficient window reads the window sum of shifted coefficients below the
cut. -/
theorem mulTail_pointTail_apply (f : MeromorphicFunction X) (D : Divisor X) (p : X)
    (s : Finset ℤ) (φ : ℤ → ℂ) (p' : X) (m : ℤ) :
    mulTail f D (∑ j ∈ s, Finsupp.single (p, j) (φ j)) (p', m)
      = if p' = p ∧ m < -(D p) then ∑ j ∈ s, φ j * f.coeffAt p (m - j) else 0 := by
  classical
  rw [map_sum, Finsupp.finsetSum_apply]
  have hterm : ∀ j ∈ s, (mulTail f D (Finsupp.single (p, j) (φ j))) (p', m)
      = if p' = p ∧ m < -(D p) then φ j * f.coeffAt p (m - j) else 0 := by
    intro j _
    rw [mulTail_single, Finsupp.smul_apply, mulTailSingle_apply, smul_eq_mul]
    split
    · rfl
    · rw [mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hcond : p' = p ∧ m < -(D p)
  · rw [if_pos hcond]
    exact Finset.sum_congr rfl fun j _ => by rw [if_pos hcond]
  · rw [if_neg hcond]
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg hcond]

/-! ### Linearity of `mulTail` in the function -/

theorem mulTailSingle_add (f g : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ) :
    mulTailSingle (f + g) D q = mulTailSingle f D q + mulTailSingle g D q := by
  obtain ⟨p, k⟩ := q
  ext q'
  obtain ⟨p', m⟩ := q'
  rw [Finsupp.add_apply, mulTailSingle_apply, mulTailSingle_apply, mulTailSingle_apply,
    MeromorphicFunction.coeffAt_add]
  split <;> simp

theorem mulTailSingle_smul (a : ℂ) (f : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ) :
    mulTailSingle (a • f) D q = a • mulTailSingle f D q := by
  obtain ⟨p, k⟩ := q
  ext q'
  obtain ⟨p', m⟩ := q'
  rw [Finsupp.smul_apply, mulTailSingle_apply, mulTailSingle_apply,
    MeromorphicFunction.coeffAt_smul, smul_eq_mul]
  split <;> simp

theorem mulTailSingle_eq_zero_of_germZero {f : MeromorphicFunction X}
    (hf : f ∈ germZeroSubmodule (X := X)) (D : Divisor X) (q : X × ℤ) :
    mulTailSingle f D q = 0 := by
  obtain ⟨p, k⟩ := q
  ext q'
  obtain ⟨p', m⟩ := q'
  rw [mulTailSingle_apply, Finsupp.coe_zero, Pi.zero_apply,
    MeromorphicFunction.coeffAt_of_orderW_eq_top (hf p)]
  split <;> rfl

theorem mulTail_add_fun (f g : MeromorphicFunction X) (D : Divisor X) :
    mulTail (f + g) D = mulTail f D + mulTail g D := by
  refine Finsupp.lhom_ext fun q a => ?_
  rw [LinearMap.add_apply, mulTail_single, mulTail_single, mulTail_single,
    mulTailSingle_add, smul_add]

theorem mulTail_smul_fun (a : ℂ) (f : MeromorphicFunction X) (D : Divisor X) :
    mulTail (a • f) D = a • mulTail f D := by
  refine Finsupp.lhom_ext fun q b => ?_
  rw [LinearMap.smul_apply, mulTail_single, mulTail_single, mulTailSingle_smul,
    smul_comm]

theorem mulTail_eq_zero_of_germZero {f : MeromorphicFunction X}
    (hf : f ∈ germZeroSubmodule (X := X)) (D : Divisor X) :
    mulTail f D = 0 := by
  refine Finsupp.lhom_ext fun q a => ?_
  rw [mulTail_single, mulTailSingle_eq_zero_of_germZero hf D q, smul_zero,
    LinearMap.zero_apply]

/-! ### The upper kill and the transport identity -/

/-- **The upper kill**: for `f ∈ L(E)`, `mulTail f D` annihilates the upper space
`𝒰[D−E]` (the truncation depth clears the multiplier's pole bound). -/
theorem mulTail_eq_zero_of_mem_upperSpace {E : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) E) (D : Divisor X) {u : GlobalTails X}
    (hu : u ∈ upperSpace (D - E)) : mulTail f D u = 0 := by
  classical
  rw [mulTail_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨p, k⟩ := q
  have hcut : -(D p) + E p ≤ k := by
    have hmem := hu hq
    simp only [Set.mem_compl_iff, belowSet, Set.mem_setOf_eq, not_lt, Finsupp.sub_apply]
      at hmem
    omega
  have hzero : mulTailSingle f D (p, k) = 0 := by
    ext q'
    obtain ⟨p', m⟩ := q'
    rw [mulTailSingle_apply, Finsupp.coe_zero, Pi.zero_apply]
    split
    · rename_i hcond
      refine MeromorphicFunction.coeffAt_eq_zero_of_coe_lt_orderW ?_
      refine lt_of_lt_of_le ?_ (hf p)
      exact_mod_cast (by omega : m - k < -(E p))
    · rfl
  rw [hzero, smul_zero]

/-- **The transport identity** (the engine of the descended multiplication): for
`f ∈ L(E)`, multiplying the level-`(D−E)` tail of `g` and truncating at `D` is the
level-`D` tail of `f·g`: `mulTail f D (α_{D−E} g) = α_D (f·g)`. -/
theorem mulTail_tailMap {E : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) E) (D : Divisor X) (g : MeromorphicFunction X) :
    mulTail f D (tailMap (D - E) g) = tailMap D (f * g) := by
  classical
  ext q
  obtain ⟨p, m⟩ := q
  rw [show tailMap (D - E) g = tailMapFun (D - E) g from rfl, tailMapFun, map_sum,
    Finsupp.finsetSum_apply, tailMap_apply_coeff]
  set S : Finset X := (D - E).support ∪ g.div.support with hS
  have hterm : ∀ p' ∈ S,
      (mulTail f D (∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
        (-((D - E : Divisor X) p')), Finsupp.single (p', k) (g.coeffAt p' k))) (p, m)
      = if p = p' ∧ m < -(D p') then
          ∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
            (-((D - E : Divisor X) p')), g.coeffAt p' k * f.coeffAt p' (m - k)
        else 0 := by
    intro p' _
    exact mulTail_pointTail_apply f D p' _ _ p m
  rw [Finset.sum_congr rfl hterm]
  have hsplit : ∀ p' : X, (if p = p' ∧ m < -(D p') then
      ∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
        (-((D - E : Divisor X) p')), g.coeffAt p' k * f.coeffAt p' (m - k) else 0)
      = if p = p' then (if m < -(D p') then
          ∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
            (-((D - E : Divisor X) p')), g.coeffAt p' k * f.coeffAt p' (m - k) else 0)
        else 0 := by
    intro p'
    by_cases h1 : p = p'
    · by_cases h2 : m < -(D p')
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
      · rw [if_neg (by tauto), if_pos h1, if_neg h2]
    · rw [if_neg (by tauto), if_neg h1]
  rw [Finset.sum_congr rfl fun p' _ => hsplit p']
  rw [Finset.sum_ite_eq S p fun p' => if m < -(D p') then
      ∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
        (-((D - E : Divisor X) p')), g.coeffAt p' k * f.coeffAt p' (m - k) else 0]
  -- the window product law identifies the windowed sum with the product coefficient
  have hwindow : m < -(D p) →
      (f * g).coeffAt p m
        = ∑ k ∈ Finset.Ico (min ((g.orderW p).untop₀) (-((D - E : Divisor X) p)))
            (-((D - E : Divisor X) p)), g.coeffAt p k * f.coeffAt p (m - k) := by
    intro hm
    refine MeromorphicFunction.coeffAt_mul_window f g p
      (coe_min_untop₀_le_self _ _) (min_le_right _ _) ?_
    refine le_trans ?_ (hf p)
    have harith : m + 1 - (-((D - E : Divisor X) p)) ≤ -(E p) := by
      rw [Finsupp.sub_apply]
      omega
    exact_mod_cast harith
  by_cases hmem : p ∈ S
  · rw [if_pos hmem]
    by_cases hm : m < -(D p)
    · rw [if_pos hm, if_pos hm, hwindow hm]
    · rw [if_neg hm, if_neg hm]
  · rw [if_neg hmem]
    rw [Finset.mem_union, not_or] at hmem
    by_cases hm : m < -(D p)
    · rw [if_pos hm]
      have hDE0 : (D - E : Divisor X) p = 0 := Finsupp.notMem_support_iff.mp hmem.1
      have hEp : E p = D p := by
        have := Finsupp.sub_apply (g₁ := D) (g₂ := E) (a := p)
        rw [hDE0] at this
        omega
      have hgord : (0 : WithTop ℤ) ≤ g.orderW p :=
        MeromorphicFunction.orderW_nonneg_of_not_mem_div_support hmem.2
      refine (MeromorphicFunction.coeffAt_eq_zero_of_coe_lt_orderW ?_).symm
      rw [MeromorphicFunction.orderW_mul]
      calc ((m : ℤ) : WithTop ℤ) < ((-(E p) : ℤ) : WithTop ℤ) := by
            exact_mod_cast (by omega : m < -(E p))
        _ ≤ f.orderW p := hf p
        _ = f.orderW p + 0 := (add_zero _).symm
        _ ≤ f.orderW p + g.orderW p := add_le_add le_rfl hgord
    · rw [if_neg hm]

end Dolbeault

end Jacobians

end

/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailDictionary
import KirovDolbeault.Dolbeault.FineResidue.GlobalCorrection

/-!
# The Čech↔tail dictionary, UNCONDITIONAL: `UnwindRegularity` for the concrete fine sheaf

The W2–W5 cocycle-side bookkeeping of `docs/planning/DICT_ROUTE.md`, on top of the W1
analytic engine (`FineResidue/GlobalCorrection.lean`).  At a forced bad point `b` that is
NOT cover-isolated (`K b = 0`, discovery D2), the single-chart skyscraper test cochain of
`SerreUnwindDetect.lean` fails level-`E` membership on star overlaps; this file builds the
**deep-matching star cochain** instead, presents the cup coboundary in the
global-cutoff-subtracted form, and runs the W1 engine to evaluate the residue functional —
removing the `BadPointsIsolated` discipline from the §17.7 chain.

* **W2 — the triangular window realization** (`exists_window_matching_section`): per star
  chart `U i ∋ b`, a section `c_i ∈ 𝒪_{Ě+b}(U i)` whose FULL ambient-chart Laurent window at
  `b` (orders `−(m+1) … −(E b+1)`) matches a prescribed meromorphic target — downward
  triangular induction on the window over `ExactOrderWitness` sections, reading invariantly
  at `b` through `Gext` and the ambient chart (`ordU_eq_orderAt_Gext`).  Packaged as
  `DeepTestData`; the deep cochain `i ↦ [c_i]` has `δ⁰c ∈ Z¹(𝒪_E)` (matching windows cancel
  on star overlaps; `b` is absent from mixed overlaps) and dies in `H¹(𝒪_D)`.
* **W3 — the X-side cutoff** `θ` (a `SmoothBumpFunction` at `b` with support inside
  `U j₀ ∖ posSupp K`), the global correction scalar `H := θ·h⁰_{j₀}`, and the repaired
  presentation `h̃_i := repairAtX b (h⁰_i − H)`.
* **W4 — the presentation bookkeeping**: `h̃` is smooth at `b` (the matching principal parts
  cancel: `ord ≥ n − E b ≥ 0`), `IsCoboundaryOn` survives the repair by continuity (the
  level-`K` cocycle is honest at `b` since `K b = 0`), `SlotProductExtendsAt` at the
  unmarked K-points is inherited from the vanish engine (`supp θ` avoids them), and the
  marked simple-pole shape comes from the (component-generalized)
  `exists_slotProductSimplePoleAt`.
* **W5 — assembly**: `unwindRegularity_concrete` (case split: cover-isolated bad point →
  the proven `SerreUnwindDetect` engine; otherwise → the W2–W4 construction into the W1
  engine), then `cechTailComparison_concrete` and `pairing_surjective_concrete`.

References: Forster (GTM 81) Lemma 17.7; Miranda (GSM 5) VI.3.6;
`docs/planning/DICT_ROUTE.md` (D1–D3, W-table), `docs/planning/DICT_BLOCKER.md`.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Filter Module Complex
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace Dolbeault

open FineResidue

variable {𝔇 : ChartDiskCover X}

/-! ## Part 0 — planar and `Gext` helpers -/

/-- A meromorphic function of nonnegative order agrees, on a punctured neighbourhood, with an
analytic function (the normal form; `q := 0` at order `⊤`). -/
theorem exists_analyticAt_extension {F : ℂ → ℂ} {c : ℂ} (hF : MeromorphicAt F c)
    (h0 : (0 : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q c ∧ F =ᶠ[𝓝[≠] c] q := by
  rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
  · refine ⟨0, analyticAt_const, ?_⟩
    have h := meromorphicOrderAt_eq_top_iff.mp htop
    filter_upwards [h] with z hz
    exact hz
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    have hn0 : 0 ≤ n := by
      rw [← hn] at h0
      exact_mod_cast h0
    obtain ⟨w, hwan, _, hwe⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hn.symm
    refine ⟨fun z => (z - c) ^ n.toNat * w z, ?_, ?_⟩
    · exact (((analyticAt_id.sub analyticAt_const).pow _).mul hwan)
    · filter_upwards [hwe] with z hz
      rw [hz, smul_eq_mul]
      congr 1
      rw [show (z - c) ^ n = (z - c) ^ ((n.toNat : ℤ)) from by rw [Int.toNat_of_nonneg hn0],
        zpow_natCast]

/-- One `WithTop ℤ` upgrade step: strict `l < ord` gives `l + 1 ≤ ord`. -/
private theorem add_one_le_of_lt' {l : ℤ} {o : WithTop ℤ} (hl : (l : WithTop ℤ) < o) :
    ((l + 1 : ℤ) : WithTop ℤ) ≤ o := by
  cases o with
  | top => exact le_top
  | coe v =>
    have hv : l < v := by exact_mod_cast hl
    exact_mod_cast hv

/-- Constant rescales preserve planar meromorphy. -/
private theorem meromorphicAt_const_smul {F : ℂ → ℂ} {c : ℂ} (s : ℂ)
    (hF : MeromorphicAt F c) : MeromorphicAt (s • F) c := by
  have h := ((analyticAt_const (v := s) (x := c)).meromorphicAt).smul hF
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp

/-- Constant nonzero rescales preserve the planar meromorphic order. -/
private theorem meromorphicOrderAt_const_smul {F : ℂ → ℂ} {c : ℂ} {s : ℂ} (hs : s ≠ 0) :
    meromorphicOrderAt (s • F) c = meromorphicOrderAt F c := by
  have h : (s • F) = (fun _ : ℂ => s) • F := by
    funext z
    simp
  rw [h]
  exact meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hs)

/-- `laurentCoeff` is subtractive on functions of order `≥ k`. -/
theorem laurentCoeff_sub {k : ℤ} {F G : ℂ → ℂ} {c : ℂ}
    (hF : MeromorphicAt F c) (hG : MeromorphicAt G c)
    (hordF : (k : WithTop ℤ) ≤ meromorphicOrderAt F c)
    (hordG : (k : WithTop ℤ) ≤ meromorphicOrderAt G c) :
    laurentCoeff k (F - G) c = laurentCoeff k F c - laurentCoeff k G c := by
  have hneg : F - G = F + (-1 : ℂ) • G := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hordG' : (k : WithTop ℤ) ≤ meromorphicOrderAt ((-1 : ℂ) • G) c := by
    rwa [meromorphicOrderAt_const_smul (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [hneg, laurentCoeff_add hF (meromorphicAt_const_smul _ hG) hordF hordG',
    laurentCoeff_smul (-1 : ℂ) hG hordG]
  simp only [smul_eq_mul]
  ring

/-- The order of a difference is at least the minimum of the orders. -/
theorem min_le_meromorphicOrderAt_sub {F G : ℂ → ℂ} {c : ℂ}
    (hF : MeromorphicAt F c) (hG : MeromorphicAt G c) :
    min (meromorphicOrderAt F c) (meromorphicOrderAt G c)
      ≤ meromorphicOrderAt (F - G) c := by
  have hneg : F - G = F + (-1 : ℂ) • G := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hGord : meromorphicOrderAt ((-1 : ℂ) • G) c = meromorphicOrderAt G c :=
    meromorphicOrderAt_const_smul (by norm_num)
  rw [hneg]
  refine le_trans (le_of_eq ?_) (meromorphicOrderAt_add hF (meromorphicAt_const_smul _ hG))
  rw [hGord]

/-- **Strictly dominated sums keep the smaller order**: `ord F = n < ord G ⟹ ord (F+G) = n`. -/
theorem meromorphicOrderAt_add_of_lt {F G : ℂ → ℂ} {c : ℂ} {n : ℤ}
    (hF : MeromorphicAt F c) (hG : MeromorphicAt G c)
    (hFn : meromorphicOrderAt F c = (n : WithTop ℤ))
    (hlt : (n : WithTop ℤ) < meromorphicOrderAt G c) :
    meromorphicOrderAt (F + G) c = (n : WithTop ℤ) := by
  have hsum : MeromorphicAt (F + G) c := hF.add hG
  have hge : (n : WithTop ℤ) ≤ meromorphicOrderAt (F + G) c := by
    refine le_trans ?_ (meromorphicOrderAt_add hF hG)
    rw [hFn]
    exact le_min le_rfl (le_of_lt hlt)
  -- the order-`n` coefficient of the sum is the (nonzero) coefficient of `F`
  have hcF : laurentCoeff n F c ≠ 0 := by
    intro h0
    have := (laurentCoeff_eq_zero_iff hF (le_of_eq hFn.symm)).mp h0
    rw [hFn] at this
    exact lt_irrefl _ this
  have hcG : laurentCoeff n G c = 0 :=
    (laurentCoeff_eq_zero_iff hG (le_of_lt hlt)).mpr hlt
  have hcsum : laurentCoeff n (F + G) c ≠ 0 := by
    rw [laurentCoeff_add hF hG (le_of_eq hFn.symm) (le_of_lt hlt), hcG, add_zero]
    exact hcF
  -- nonzero coefficient pins the order to `≤ n`
  have hle : meromorphicOrderAt (F + G) c ≤ (n : WithTop ℤ) := by
    by_contra hgt
    push_neg at hgt
    exact hcsum ((laurentCoeff_eq_zero_iff hsum hge).mpr hgt)
  exact le_antisymm hle hge

variable {b : X}

/-- The ambient chart point at `b` (the common read point of all window matches). -/
private abbrev βpt (b : X) : ℂ := (chartAt (H := ℂ) b) b

/-- The ambient read of a section through `Gext` and the chart at `b`. -/
private abbrev ambRead {U : Opens X} (c : ↥U → ℂ) (b : X) : ℂ → ℂ :=
  Gext c ∘ (chartAt (H := ℂ) b).symm

/-- The ambient read of a member of `OmegaD` is meromorphic at `βpt b` with order `ordU`. -/
theorem ambRead_meromorphicAt {U : Opens X} {c : ↥U → ℂ} {D' : Divisor X}
    (hc : c ∈ OmegaD D' U) (hb : b ∈ U) :
    MeromorphicAt (ambRead c b) (βpt b) :=
  Gext_meromorphicAt hc.1 hb

/-- Divisor bookkeeping: the window package at `b`, away from `b`. -/
private theorem window_divisor_apply_ne {E : Divisor X} {m : ℤ} {x : X} (hx : x ≠ b) :
    (E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) x = E x := by
  rw [Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (a := b) (a' := x) hx,
    Finsupp.single_eq_of_ne (a := b) (a' := x) hx]
  ring

/-- Divisor bookkeeping: the window package at `b`, at `b`. -/
private theorem window_divisor_apply_self {E : Divisor X} {m : ℤ} :
    (E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) b = m + 1 := by
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_same]
  ring

/-- Window packages are monotone in the window length. -/
theorem OmegaD_window_mono {E : Divisor X} {U : Opens X} {m m' : ℤ} (hm : m ≤ m')
    (hEm : E b ≤ m) :
    OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) U
      ≤ OmegaD (E + Finsupp.single b (m' - E b) + Finsupp.single b 1) U := by
  refine OmegaD_mono fun x _ => ?_
  by_cases hx : x = b
  · subst hx
    rw [window_divisor_apply_self, window_divisor_apply_self]
    omega
  · rw [window_divisor_apply_ne hx, window_divisor_apply_ne hx]

/-- **Pole-bound transfer off a marked point**: a section satisfying the window package whose
order at `b` meets the `𝒪_E` bound lies in `𝒪_E`. -/
theorem mem_OmegaD_of_window_of_ordU {E : Divisor X} {m : ℤ} {U : Opens X} {f : ↥U → ℂ}
    (hf : f ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) U)
    (hb : b ∈ U) (hord : ((-(E b) : ℤ) : WithTop ℤ) ≤ ordU f ⟨b, hb⟩) :
    f ∈ OmegaD E U := by
  refine ⟨hf.1, fun x => ?_⟩
  by_cases hx : x.1 = b
  · have hxb : x = ⟨b, hb⟩ := Subtype.ext hx
    rw [hxb]
    exact_mod_cast hord
  · have h := hf.2 x
    rwa [show (-((E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) x.1)
        : WithTop ℤ) = (-(E x.1) : WithTop ℤ) from by
      rw [window_divisor_apply_ne hx]] at h

/-! ## Part 1 — W2: the triangular window realization

At a marked point `b ∈ U j`, build a section of the window package
`𝒪_{E + (m−E b)·b + b}(U j)` whose ambient-chart Laurent window at `b` (orders
`−(m+1) … −(E b+1)`) matches a prescribed meromorphic target `t`: realize the lowest-order
coefficient by a scaled `ExactOrderWitness` section, subtract, recurse upward. -/

/-- The "target already regular" case: the zero section matches. -/
private theorem window_zero_case {j : 𝔇.toFiniteCover.ι} {E : Divisor X} {m : ℤ}
    {t : ℂ → ℂ} (hcase : ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b)) :
    (0 : ↥(𝔇.U j) → ℂ)
        ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) ∧
      ((-(E b) : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt (ambRead (0 : ↥(𝔇.U j) → ℂ) b - t) (βpt b) := by
  refine ⟨Submodule.zero_mem _, ?_⟩
  have hread : ambRead (0 : ↥(𝔇.U j) → ℂ) b - t = (-1 : ℂ) • t := by
    funext z
    simp only [Pi.sub_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [show Gext (0 : ↥(𝔇.U j) → ℂ) ((chartAt (H := ℂ) b).symm z) = 0 from by
      unfold Gext
      split <;> rfl]
    ring
  rw [hread, meromorphicOrderAt_const_smul (by norm_num : (-1 : ℂ) ≠ 0)]
  exact hcase

/-- **The cancellation step**: a target of exact finite window order `n` is matched at its
lowest-order coefficient by a scaled `ExactOrderWitness` section, strictly raising the order
of the residual. -/
private theorem window_cancel_step (hwit : ExactOrderWitness 𝔇)
    {j : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j : Set X)) (E : Divisor X) {m n : ℤ}
    (hEm : E b ≤ m) {t : ℂ → ℂ} (ht : MeromorphicAt t (βpt b))
    (hn : meromorphicOrderAt t (βpt b) = (n : WithTop ℤ))
    (hge : -m - 1 ≤ n) (hlt : n < -E b) :
    ∃ c₀ : ↥(𝔇.U j) → ℂ,
      c₀ ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) ∧
      MeromorphicAt (ambRead c₀ b) (βpt b) ∧
      ((n + 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (t - ambRead c₀ b) (βpt b) := by
  classical
  set d' : ℤ := -n - 1 - E b with hd'def
  have hd'0 : 0 ≤ d' := by omega
  have hd'm : d' ≤ m - E b := by omega
  -- the witness section of exact order `n` at `b`
  obtain ⟨γ', hγmem, hγord⟩ := hwit (E + Finsupp.single b d') j b hb
  have hDb : (E + Finsupp.single b d' : Divisor X) b = E b + d' := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
  have hγordn : ordU γ' ⟨b, hb⟩ = (n : WithTop ℤ) := by
    rw [hγord, hDb]
    congr 1
    omega
  -- repackage the membership into the window package
  have harg : (E b + d') - E b = d' := by ring
  have hγmem' : γ' ∈ OmegaD
      (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) := by
    refine OmegaD_window_mono (by omega : E b + d' ≤ m) (by omega) ?_
    rw [harg]
    exact hγmem
  -- the ambient read of the witness has exact order `n`
  have hγmer : MeromorphicAt (ambRead γ' b) (βpt b) := ambRead_meromorphicAt hγmem' hb
  have hreadord : meromorphicOrderAt (ambRead γ' b) (βpt b) = (n : WithTop ℤ) := by
    rw [show meromorphicOrderAt (ambRead γ' b) (βpt b)
        = ordU γ' ⟨b, hb⟩ from (ordU_eq_orderAt_Gext γ' hb).symm]
    exact hγordn
  -- the leading coefficients
  set lt : ℂ := laurentCoeff n t (βpt b) with hltdef
  set lγ : ℂ := laurentCoeff n (ambRead γ' b) (βpt b) with hlγdef
  have hlt0 : lt ≠ 0 := by
    intro h0
    have := (laurentCoeff_eq_zero_iff ht (le_of_eq hn.symm)).mp h0
    rw [hn] at this
    exact lt_irrefl _ this
  have hlγ0 : lγ ≠ 0 := by
    intro h0
    have := (laurentCoeff_eq_zero_iff hγmer (le_of_eq hreadord.symm)).mp h0
    rw [hreadord] at this
    exact lt_irrefl _ this
  set s : ℂ := lt / lγ with hsdef
  have hs0 : s ≠ 0 := div_ne_zero hlt0 hlγ0
  refine ⟨s • γ', Submodule.smul_mem _ s hγmem', ?_, ?_⟩
  all_goals
    have hreadsmul : ambRead (s • γ') b = s • ambRead γ' b := by
      funext z
      show Gext (s • γ') ((chartAt (H := ℂ) b).symm z) = s • Gext γ' ((chartAt (H := ℂ) b).symm z)
      rw [Gext_smul]
      rfl
  · rw [hreadsmul]
    exact meromorphicAt_const_smul s hγmer
  · have hsmer : MeromorphicAt (s • ambRead γ' b) (βpt b) := meromorphicAt_const_smul s hγmer
    have hsord : meromorphicOrderAt (s • ambRead γ' b) (βpt b) = (n : WithTop ℤ) := by
      rw [meromorphicOrderAt_const_smul hs0]
      exact hreadord
    have hscoeff : laurentCoeff n (s • ambRead γ' b) (βpt b) = lt := by
      rw [laurentCoeff_smul s hγmer (le_of_eq hreadord.symm), ← hlγdef, smul_eq_mul, hsdef,
        div_mul_cancel₀ lt hlγ0]
    have htsub : MeromorphicAt (t - s • ambRead γ' b) (βpt b) := ht.sub hsmer
    have hsubge : (n : WithTop ℤ) ≤ meromorphicOrderAt (t - s • ambRead γ' b) (βpt b) := by
      refine le_trans ?_ (min_le_meromorphicOrderAt_sub ht hsmer)
      rw [hn, hsord, min_self]
    have hcoeff0 : laurentCoeff n (t - s • ambRead γ' b) (βpt b) = 0 := by
      rw [laurentCoeff_sub ht hsmer (le_of_eq hn.symm) (le_of_eq hsord.symm), hscoeff]
      exact sub_self lt
    have hstrict := (laurentCoeff_eq_zero_iff htsub hsubge).mp hcoeff0
    rw [hreadsmul]
    exact add_one_le_of_lt' hstrict

/-- The induction core: window length bounded by `N`. -/
private theorem exists_window_matching_aux (hwit : ExactOrderWitness 𝔇)
    {j : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j : Set X)) (E : Divisor X) :
    ∀ (N : ℕ) (m : ℤ), E b ≤ m → m - E b ≤ (N : ℤ) →
      ∀ t : ℂ → ℂ, MeromorphicAt t (βpt b) →
        ((-m - 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b) →
        ∃ c : ↥(𝔇.U j) → ℂ,
          c ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) ∧
          ((-(E b) : ℤ) : WithTop ℤ)
            ≤ meromorphicOrderAt (ambRead c b - t) (βpt b) := by
  intro N
  induction N with
  | zero =>
    intro m hEm hN t ht hord
    by_cases hcase : ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b)
    · exact ⟨0, window_zero_case hcase⟩
    · -- exactly one window slot: cancel the leading coefficient with the scaled witness
      push_neg at hcase
      have hm : m = E b := by omega
      obtain ⟨n, hn, hge, hlt⟩ : ∃ n : ℤ, meromorphicOrderAt t (βpt b) = (n : WithTop ℤ) ∧
          -m - 1 ≤ n ∧ n < -E b := by
        have hne : meromorphicOrderAt t (βpt b) ≠ ⊤ := fun hc => by
          rw [hc] at hcase
          exact absurd le_top (not_le.mpr hcase)
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
        refine ⟨n, hn.symm, ?_, ?_⟩
        · rw [← hn] at hord
          exact_mod_cast hord
        · rw [← hn] at hcase
          exact_mod_cast hcase
      obtain ⟨c₀, hc₀mem, hc₀mer, hc₀ord⟩ := window_cancel_step hwit hb E hEm ht hn hge hlt
      refine ⟨c₀, hc₀mem, ?_⟩
      -- `n + 1 = −E b` here: the residual is already regular
      have hread : ambRead c₀ b - t = (-1 : ℂ) • (t - ambRead c₀ b) := by
        funext z
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hread, meromorphicOrderAt_const_smul (by norm_num : (-1 : ℂ) ≠ 0)]
      refine le_trans (le_of_eq ?_) hc₀ord
      congr 1
      omega
  | succ N ih =>
    intro m hEm hN t ht hord
    by_cases hcase : ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b)
    · exact ⟨0, window_zero_case hcase⟩
    · push_neg at hcase
      obtain ⟨n, hn, hge, hlt⟩ : ∃ n : ℤ, meromorphicOrderAt t (βpt b) = (n : WithTop ℤ) ∧
          -m - 1 ≤ n ∧ n < -E b := by
        have hne : meromorphicOrderAt t (βpt b) ≠ ⊤ := fun hc => by
          rw [hc] at hcase
          exact absurd le_top (not_le.mpr hcase)
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
        refine ⟨n, hn.symm, ?_, ?_⟩
        · rw [← hn] at hord
          exact_mod_cast hord
        · rw [← hn] at hcase
          exact_mod_cast hcase
      obtain ⟨c₀, hc₀mem, hc₀mer, hc₀ord⟩ := window_cancel_step hwit hb E hEm ht hn hge hlt
      set t₁ : ℂ → ℂ := t - ambRead c₀ b with ht₁def
      have ht₁mer : MeromorphicAt t₁ (βpt b) := ht.sub hc₀mer
      by_cases hcase₁ : ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t₁ (βpt b)
      · -- the residual is already regular: `c₀` matches
        refine ⟨c₀, hc₀mem, ?_⟩
        have hread : ambRead c₀ b - t = (-1 : ℂ) • t₁ := by
          funext z
          simp only [ht₁def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hread, meromorphicOrderAt_const_smul (by norm_num : (-1 : ℂ) ≠ 0)]
        exact hcase₁
      · -- recurse on the strictly shorter window `[n+1, −E b)`
        push_neg at hcase₁
        have hn1 : n + 1 < -E b := by
          rcases lt_or_ge (n + 1) (-E b) with h | h
          · exact h
          · exfalso
            exact absurd (le_trans (by exact_mod_cast h) hc₀ord) (not_le.mpr hcase₁)
        set m₁ : ℤ := -n - 2 with hm₁def
        have hEm₁ : E b ≤ m₁ := by omega
        have hN₁ : m₁ - E b ≤ (N : ℤ) := by
          have : (↑(N + 1) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
          omega
        have hord₁ : ((-m₁ - 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t₁ (βpt b) := by
          refine le_trans (le_of_eq ?_) hc₀ord
          congr 1
          omega
        obtain ⟨c₁, hc₁mem, hc₁ord⟩ := ih m₁ hEm₁ hN₁ t₁ ht₁mer hord₁
        refine ⟨c₀ + c₁, ?_, ?_⟩
        · exact Submodule.add_mem _ hc₀mem
            (OmegaD_window_mono (by omega : m₁ ≤ m) hEm₁ hc₁mem)
        · have hread : ambRead (c₀ + c₁) b - t = ambRead c₁ b - t₁ := by
            funext z
            show Gext (c₀ + c₁) ((chartAt (H := ℂ) b).symm z) - t z
              = Gext c₁ ((chartAt (H := ℂ) b).symm z) - t₁ z
            rw [Gext_add]
            simp only [ht₁def, Pi.add_apply, Pi.sub_apply, Function.comp_apply]
            ring
          rw [hread]
          exact hc₁ord

/-- **W2 — the triangular window realization** (`DICT_ROUTE.md` W2): at a marked point
`b ∈ U j` of a cover with the `ExactOrderWitness`, every meromorphic target `t` of ambient
order `≥ −(m+1)` is matched, through the full Laurent window `−(m+1) … −(E b+1)`, by a
section of the window package `𝒪_{E + (m−E b)·b + b}(U j)`: the difference of the ambient
reads has order `≥ −E b` at `b`. -/
theorem exists_window_matching_section (hwit : ExactOrderWitness 𝔇)
    {j : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j : Set X)) (E : Divisor X) {m : ℤ}
    (hEm : E b ≤ m) {t : ℂ → ℂ} (ht : MeromorphicAt t (βpt b))
    (hord : ((-m - 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b)) :
    ∃ c : ↥(𝔇.U j) → ℂ,
      c ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) ∧
      ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (ambRead c b - t) (βpt b) :=
  exists_window_matching_aux hwit hb E (m - E b).toNat m hEm (Int.self_le_toNat _) t ht hord

/-- Reads through the ambient chart at `b` agree near `βpt b` whenever the `X`-side functions
agree on an open set containing `b`. -/
theorem read_eventuallyEq_of_eqOn {F G : X → ℂ} {V : Set X} (hV : IsOpen V) (hbV : b ∈ V)
    (hFG : ∀ x ∈ V, F x = G x) :
    F ∘ (chartAt (H := ℂ) b).symm =ᶠ[𝓝 (βpt b)] G ∘ (chartAt (H := ℂ) b).symm := by
  have hb' : b ∈ (chartAt (H := ℂ) b).source := mem_chart_source ℂ b
  have hcont : ContinuousAt (chartAt (H := ℂ) b).symm (βpt b) :=
    (chartAt (H := ℂ) b).continuousAt_symm ((chartAt (H := ℂ) b).map_source hb')
  have hli : (chartAt (H := ℂ) b).symm (βpt b) = b := (chartAt (H := ℂ) b).left_inv hb'
  have hmem : ∀ᶠ ζ in 𝓝 (βpt b), (chartAt (H := ℂ) b).symm ζ ∈ V := by
    refine hcont.preimage_mem_nhds ?_
    rw [hli]
    exact hV.mem_nhds hbV
  filter_upwards [hmem] with ζ hζ
  exact hFG _ hζ

/-- Restriction membership for `OmegaD` by precomposition with the open inclusion. -/
theorem OmegaD_comp_openIncl {D' : Divisor X} {U V : Opens X} (h : V ≤ U) {f : ↥U → ℂ}
    (hf : f ∈ OmegaD D' U) : f ∘ openIncl h ∈ OmegaD D' V :=
  ⟨isMeromorphic_comp_openIncl h hf.1, fun v => by
    rw [ordU_comp_openIncl]
    exact hf.2 _⟩

/-! ## Part 2 — the deep-matching star cochain (`DeepTestData`)

The multi-chart replacement of `TestCocycleData` at a possibly non-isolated marked point:
one section per star chart, all matching a COMMON ambient window target `t` of exact order
`−(m+1)` at `b`.  Pairwise differences then meet the `𝒪_E` bound at `b`, so the coboundary
is a `Z¹(𝒪_E)` test cocycle trivialized at level `D` by the cochain itself. -/

variable {E : Divisor X} {m : ℤ}

/-- **The deep-matching star test datum** at `(E, b, m)`: a common ambient window target `t`
of exact order `−(m+1)` at `b`, and per-chart sections of the window package matching `t`
through the full window (zero off the star). -/
structure DeepTestData (𝔇 : ChartDiskCover X) (E : Divisor X) (b : X) (m : ℤ) where
  /-- The window bound `E b ≤ m`. -/
  hmE : E b ≤ m
  /-- The common ambient window target. -/
  t : ℂ → ℂ
  /-- The target is meromorphic at the ambient chart point. -/
  tmer : MeromorphicAt t (βpt b)
  /-- The target has exact order `−(m+1)`. -/
  tord : meromorphicOrderAt t (βpt b) = ((-m - 1 : ℤ) : WithTop ℤ)
  /-- The per-chart sections. -/
  c : ∀ i : 𝔇.toFiniteCover.ι, ↥(𝔇.U i) → ℂ
  /-- Star sections satisfy the window package bounds. -/
  mem : ∀ i, ∀ _ : b ∈ (𝔇.U i : Set X),
    c i ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U i)
  /-- Off-star sections vanish. -/
  zero : ∀ i, b ∉ (𝔇.U i : Set X) → c i = 0
  /-- Star sections match the target through the full window. -/
  matched : ∀ i, ∀ _ : b ∈ (𝔇.U i : Set X),
    ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (ambRead (c i) b - t) (βpt b)

/-- The deep test datum exists on any cover with the exact-order witness (the common target
is the ambient read of the distinguished-chart witness section). -/
theorem DeepTestData.exists_of_witness (hwit : ExactOrderWitness 𝔇)
    {j₀ : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j₀ : Set X)) (hmE : E b ≤ m) :
    Nonempty (DeepTestData 𝔇 E b m) := by
  classical
  -- the distinguished witness section and its ambient read
  obtain ⟨γ, hγmem, hγord⟩ := hwit (E + Finsupp.single b (m - E b)) j₀ b hb
  have hDb : (E + Finsupp.single b (m - E b) : Divisor X) b = m := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
    ring
  have hγordm : ordU γ ⟨b, hb⟩ = ((-m - 1 : ℤ) : WithTop ℤ) := by
    rw [hγord, hDb]
  set t : ℂ → ℂ := ambRead γ b with htdef
  have hγmer : IsMeromorphic ((𝔇.U j₀ : Opens X) : Type _) γ := hγmem.1
  have tmer : MeromorphicAt t (βpt b) := Gext_meromorphicAt hγmer hb
  have tord : meromorphicOrderAt t (βpt b) = ((-m - 1 : ℤ) : WithTop ℤ) := by
    rw [htdef, show meromorphicOrderAt (ambRead γ b) (βpt b) = ordU γ ⟨b, hb⟩ from
      (ordU_eq_orderAt_Gext γ hb).symm]
    exact hγordm
  -- per-chart matching sections
  have hsec : ∀ i : 𝔇.toFiniteCover.ι, ∃ ci : ↥(𝔇.U i) → ℂ,
      (b ∈ (𝔇.U i : Set X) →
        ci ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U i) ∧
        ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (ambRead ci b - t) (βpt b)) ∧
      (b ∉ (𝔇.U i : Set X) → ci = 0) := by
    intro i
    by_cases hi : b ∈ (𝔇.U i : Set X)
    · obtain ⟨ci, hcm, hco⟩ := exists_window_matching_section hwit hi E hmE tmer
        (le_of_eq tord.symm)
      exact ⟨ci, fun _ => ⟨hcm, hco⟩, fun h => absurd hi h⟩
    · exact ⟨0, fun h => absurd h hi, fun _ => rfl⟩
  choose cfun hstar hoff using hsec
  exact ⟨⟨hmE, t, tmer, tord, cfun, fun i hi => (hstar i hi).1, hoff,
    fun i hi => (hstar i hi).2⟩⟩

namespace DeepTestData

variable (dd : DeepTestData 𝔇 E b m)

/-- The ambient read of a star section is meromorphic at `βpt b`. -/
theorem ambRead_mer {i : 𝔇.toFiniteCover.ι} (hi : b ∈ (𝔇.U i : Set X)) :
    MeromorphicAt (ambRead (dd.c i) b) (βpt b) :=
  ambRead_meromorphicAt (dd.mem i hi) hi

/-- **Star sections have exact order `−(m+1)` at `b`** (the target order dominates the
matching defect: `−(m+1) < −E b`). -/
theorem ordU_c {i : 𝔇.toFiniteCover.ι} (hi : b ∈ (𝔇.U i : Set X)) :
    ordU (dd.c i) ⟨b, hi⟩ = ((-m - 1 : ℤ) : WithTop ℤ) := by
  have hsplit : ambRead (dd.c i) b = dd.t + (ambRead (dd.c i) b - dd.t) := by
    funext z
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hlt : ((-m - 1 : ℤ) : WithTop ℤ)
      < meromorphicOrderAt (ambRead (dd.c i) b - dd.t) (βpt b) := by
    refine lt_of_lt_of_le ?_ (dd.matched i hi)
    have := dd.hmE
    exact_mod_cast (by omega : -m - 1 < -(E b))
  rw [ordU_eq_orderAt_Gext (dd.c i) hi]
  show meromorphicOrderAt (ambRead (dd.c i) b) (βpt b) = ((-m - 1 : ℤ) : WithTop ℤ)
  rw [hsplit]
  exact meromorphicOrderAt_add_of_lt dd.tmer ((dd.ambRead_mer hi).sub dd.tmer) dd.tord hlt

/-- The per-star-chart `TestCocycleData` package carried by the deep datum. -/
noncomputable def toTestCocycleData {i : 𝔇.toFiniteCover.ι} (hi : b ∈ (𝔇.U i : Set X)) :
    TestCocycleData 𝔇 E i b hi m :=
  ⟨dd.c i, dd.mem i hi, dd.ordU_c hi⟩

/-- **The window defect of two star sections** meets the `𝒪_E` bound at `b` (read on any
common sub-open): the two matching defects subtract. -/
theorem ordU_sub_ge {i k : 𝔇.toFiniteCover.ι} {V : Opens X} (h₁ : V ≤ 𝔇.U i)
    (h₂ : V ≤ 𝔇.U k) (hi : b ∈ (𝔇.U i : Set X)) (hk : b ∈ (𝔇.U k : Set X)) (hbV : b ∈ V) :
    ((-(E b) : ℤ) : WithTop ℤ) ≤ ordU
      ((dd.c i ∘ openIncl h₁) - (dd.c k ∘ openIncl h₂)) ⟨b, hbV⟩ := by
  set d : ↥V → ℂ := (dd.c i ∘ openIncl h₁) - (dd.c k ∘ openIncl h₂) with hddef
  -- the ambient read of the difference is the difference of the ambient reads, near `βpt b`
  have hev : ambRead d b =ᶠ[𝓝 (βpt b)] (ambRead (dd.c i) b - ambRead (dd.c k) b) := by
    have heq : ∀ x ∈ (V : Set X), Gext d x = (Gext (dd.c i) - Gext (dd.c k)) x := by
      intro x hx
      have hxi : x ∈ (𝔇.U i : Set X) := h₁ hx
      have hxk : x ∈ (𝔇.U k : Set X) := h₂ hx
      rw [Gext_apply_mem d hx, Pi.sub_apply, Gext_apply_mem (dd.c i) hxi,
        Gext_apply_mem (dd.c k) hxk]
      rfl
    exact read_eventuallyEq_of_eqOn V.isOpen hbV heq
  show ((-(E b) : ℤ) : WithTop ℤ) ≤ ordU d ⟨b, hbV⟩
  rw [ordU_eq_orderAt_Gext d hbV]
  show ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (ambRead d b) (βpt b)
  rw [meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)]
  -- subtract the two matching defects
  have hsplit : ambRead (dd.c i) b - ambRead (dd.c k) b
      = (ambRead (dd.c i) b - dd.t) - (ambRead (dd.c k) b - dd.t) := by
    funext z
    simp only [Pi.sub_apply]
    ring
  rw [hsplit]
  refine le_trans ?_ (min_le_meromorphicOrderAt_sub ((dd.ambRead_mer hi).sub dd.tmer)
    ((dd.ambRead_mer hk).sub dd.tmer))
  exact le_min (dd.matched i hi) (dd.matched k hk)

/-- The deep test 0-cochain: the germ of the matching section on each cover set. -/
noncomputable def cochain : 𝔇.toFiniteCover.toFiniteFamily.Cochain0 :=
  fun i => toGerm (𝔇.U i) (dd.c i)

theorem cochain_apply (i : 𝔇.toFiniteCover.ι) :
    dd.cochain i = toGerm (𝔇.U i) (dd.c i) := rfl

/-- **Level-`E` membership of the deep coboundary**: on star overlaps the matching windows
cancel; mixed overlaps avoid `b`; off-star components vanish. -/
theorem delta_mem_sections1 :
    𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain
      ∈ 𝔇.toFiniteCover.toFiniteFamily.sections1 E := by
  intro p
  obtain ⟨i, k⟩ := p
  have hδ : 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain (i, k)
      = rawRestrictG inf_le_right (dd.cochain k)
        - rawRestrictG inf_le_left (dd.cochain i) := by
    simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
  rw [hδ]
  by_cases hi : b ∈ (𝔇.U i : Set X) <;> by_cases hk : b ∈ (𝔇.U k : Set X)
  · -- both star: the matching windows cancel at `b`
    have hbV : b ∈ (𝔇.U i ⊓ 𝔇.U k : Opens X) := ⟨hi, hk⟩
    set d : ↥(𝔇.U i ⊓ 𝔇.U k : Opens X) → ℂ :=
      (dd.c k ∘ openIncl inf_le_right) - (dd.c i ∘ openIncl inf_le_left) with hddef
    have hcomp : rawRestrictG (inf_le_right : (𝔇.U i ⊓ 𝔇.U k : Opens X) ≤ 𝔇.U k)
          (dd.cochain k)
        - rawRestrictG (inf_le_left : (𝔇.U i ⊓ 𝔇.U k : Opens X) ≤ 𝔇.U i) (dd.cochain i)
        = toGerm _ d := by
      rw [cochain_apply, cochain_apply, rawRestrictG_coe, rawRestrictG_coe, hddef, map_sub]
    rw [hcomp]
    -- the difference satisfies the window package and the `𝒪_E` order bound at `b`
    have hdmem : d ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1)
        (𝔇.U i ⊓ 𝔇.U k) :=
      sub_mem (OmegaD_comp_openIncl _ (dd.mem k hk)) (OmegaD_comp_openIncl _ (dd.mem i hi))
    have hdord : ((-(E b) : ℤ) : WithTop ℤ) ≤ ordU d ⟨b, hbV⟩ :=
      dd.ordU_sub_ge inf_le_right inf_le_left hk hi hbV
    exact ⟨d, mem_OmegaD_of_window_of_ordU hdmem hbV hdord, rfl⟩
  · -- `i` star, `k` off-star: the overlap avoids `b`
    have h0 : dd.cochain k = 0 := by
      rw [cochain_apply, dd.zero k hk, map_zero]
    rw [h0, map_zero, zero_sub]
    refine neg_mem ?_
    refine OmegaDGerm_mono (fun x hx => ?_)
      (rawRestrictG_omegaDGerm _ ⟨dd.c i, dd.mem i hi, rfl⟩)
    have hxb : x ≠ b := fun hc => hk (hc ▸ hx.2)
    rw [window_divisor_apply_ne hxb]
  · -- `i` off-star, `k` star: symmetric
    have h0 : dd.cochain i = 0 := by
      rw [cochain_apply, dd.zero i hi, map_zero]
    rw [h0, map_zero, sub_zero]
    refine OmegaDGerm_mono (fun x hx => ?_)
      (rawRestrictG_omegaDGerm _ ⟨dd.c k, dd.mem k hk, rfl⟩)
    have hxb : x ≠ b := fun hc => hi (hc ▸ hx.1)
    rw [window_divisor_apply_ne hxb]
  · -- both off-star
    have h0i : dd.cochain i = 0 := by
      rw [cochain_apply, dd.zero i hi, map_zero]
    have h0k : dd.cochain k = 0 := by
      rw [cochain_apply, dd.zero k hk, map_zero]
    rw [h0i, h0k, map_zero, map_zero, sub_zero]
    exact Submodule.zero_mem _

/-- **Level-`D` membership of the deep cochain** (`m + 1 ≤ D b`, `E ≤ D`): the trivializing
0-cochain of the test class in `H¹(𝒪_D)`. -/
theorem cochain_mem_sections0 {D : Divisor X} (hED : ∀ x, E x ≤ D x) (hmD : m + 1 ≤ D b) :
    dd.cochain ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 D := by
  intro i
  by_cases hi : b ∈ (𝔇.U i : Set X)
  · refine OmegaDGerm_mono (D₁ := E + Finsupp.single b (m - E b) + Finsupp.single b 1)
      (fun x _ => ?_) ⟨dd.c i, dd.mem i hi, rfl⟩
    by_cases hx : x = b
    · subst hx
      rw [window_divisor_apply_self]
      exact hmD
    · rw [window_divisor_apply_ne hx]
      exact hED x
  · rw [cochain_apply, dd.zero i hi, map_zero]
    exact Submodule.zero_mem _

/-- The deep test coboundary is a cocycle (`δ¹ ∘ δ⁰ = 0`). -/
theorem delta_mem_ker :
    𝔇.toFiniteCover.toFiniteFamily.cechDelta1
      (𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain) = 0 := by
  have h := DFunLike.congr_fun
    (𝔇.toFiniteCover.toFiniteFamily.cechDelta1_comp_cechDelta0) dd.cochain
  rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h

/-- **The deep test cocycle**, as an element of `Z¹(𝒪_E)`. -/
noncomputable def cocycle : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 E) :=
  ⟨𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain,
    Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr dd.delta_mem_ker, dd.delta_mem_sections1⟩⟩

@[simp] theorem cocycle_coe :
    (dd.cocycle : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain := rfl

/-- **The deep test class dies in `H¹(𝒪_D)`**. -/
theorem h1InclMono_cocycle_eq_zero {D : Divisor X} (hED : ∀ x, E x ≤ D x)
    (hmD : m + 1 ≤ D b) :
    𝔇.toFiniteCover.h1InclMono hED (Submodule.Quotient.mk dd.cocycle) = 0 := by
  rw [𝔇.toFiniteCover.h1InclMono_mk, Submodule.Quotient.mk_eq_zero]
  rw [Submodule.submoduleOf, Submodule.mem_comap]
  exact ⟨dd.cochain, dd.cochain_mem_sections0 hED hmD, rfl⟩

/-! ## Part 3 — the cup of the deep cochain with `f ∈ L(K−E)` -/

variable {K : Divisor X}

/-- **Level-`K+b` membership of the deep cup 0-cochain** `f·ĉ`: poles cancel against the
linear-system bounds on every star chart, leaving the single marked simple excess at `b`. -/
theorem cup_mem_sections0 {f : MeromorphicFunction X}
    (hfE : f ∈ linearSystem (X := X) (K - E)) {n : ℤ}
    (hn : f.orderW b = (n : WithTop ℤ)) (hm : m = n + K b) :
    cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f dd.cochain
      ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (K + Finsupp.single b 1) := by
  intro i
  by_cases hi : b ∈ (𝔇.U i : Set X)
  · rw [cupCochain0_apply]
    exact mulConstG_omegaDGerm (mem_linearSystem_marked hfE hn hm)
      ⟨dd.c i, dd.mem i hi, rfl⟩
  · rw [cupCochain0_apply, cochain_apply, dd.zero i hi, map_zero, mul_zero]
    exact Submodule.zero_mem _

/-- The deep cup cochain restricts on the distinguished chart to the `TestCocycleData` cup
component (the input shape of the generalized `exists_slotProductSimplePoleAt`). -/
theorem cup_component_eq [DecidableEq 𝔇.toFiniteCover.ι] {f : MeromorphicFunction X}
    {j₀ : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j₀ : Set X)) :
    cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f dd.cochain j₀
      = cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f
          ((dd.toTestCocycleData hb).cochain) j₀ := by
  rw [cupCochain0_apply, cupCochain0_apply, TestCocycleData.cochain_self]
  rfl

end DeepTestData

end Dolbeault

end Jacobians

end

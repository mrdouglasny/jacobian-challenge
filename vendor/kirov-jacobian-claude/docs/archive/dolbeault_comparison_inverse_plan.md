# Dolbeault comparison — inverse direction (Čech → Dolbeault) + round-trips: plan

The forward map `dolbeault_to_cech` is DONE (sorry-free, axiom-clean). This plans the **inverse**
`cech_to_dolbeault : H¹(𝒪) → H^{0,1}` and the two round-trip identities (the last 3 sorries of the
comparison). Research pass: 2026-06-02.

## Math (Forster §15 / Griffiths–Harris)

Given a holomorphic Čech 1-cocycle `f = {f_ij}` (`δ¹f = 0`, each `f_ij ∈ 𝒪(U_i∩U_j)`) and a PoU
`{ρ_k}` subordinate to the cover:
- local primitives `η_i := ∑_k ρ_k·f_ik` (smooth on `U_i`);
- `η_i − η_j = f_ij` on overlaps (`cechCoboundary_telescoping`, DONE);
- `∂̄η_i = ∑_k (∂̄ρ_k)·f_ik` (since `f_ik` holomorphic), and on overlaps `∂̄η_i = ∂̄η_j`
  (`∂̄(η_i−η_j) = ∂̄f_ij = 0`), so the `∂̄η_i` **glue to a global `(0,1)`-form `ω`**;
- `[ω] ∈ H^{0,1}` is the image of `[f]`.
- **i-independence** of `∑_k (∂̄ρ_k)·f_ik`: on `U_i∩U_j` the difference is
  `∑_k (∂̄ρ_k)(f_ik−f_jk) = (∑_k ∂̄ρ_k)·f_ij = ∂̄(∑ρ_k)·f_ij = ∂̄(1)·f_ij = 0`.

## What Mathlib / the repo give us

| Need | Source | Status |
|---|---|---|
| `∑ᶠ k, ρ_k • g_k` smooth | `SmoothPartitionOfUnity.IsSubordinate.contMDiff_finsum_smul`, `contMDiff_smul` | ✅ Mathlib |
| PoU exists, subordinate | `exists_smoothPartitionOfUnity_subordinate` | ✅ repo |
| `η_i − η_j = f_ij` | `cechCoboundary_telescoping` | ✅ repo |
| Gluing local data → global (idx + per-point value + central agreement) | `CechH0.gluedFun` / `gluedFun_eventuallyEq` / `cechRestrictL_surjective` | ✅ repo (for **functions**; adapt to **forms/sections**) |
| holomorphic rep of a germ-class | holo + codiscrete-zero ⟹ 0 (unique rep) | needs a small lemma |
| `∂̄` of a function as a `(0,1)`-form | `RealForms.dbar` / `dbarL` (global `SmoothCFunctions`) | ✅ repo |
| **smooth-section gluing** (local `(0,1)`-forms agreeing on overlaps → global section) | — | ❌ **not in Mathlib; the key new infra** |

## ROUTE DECISION (2026-06-02): use the STANDARD GLUING route, NOT the double-sum

The canonical reference (**Forster §15/§17**; also Griffiths–Harris, Wells) builds the inverse by
**local primitives `η_i = ∑_k ρ_k f_ik` + GLUING the `∂̄η_i` into a global form**. That is the route to
use. The repo already templates the gluing: **`CechH0.gluedFun` / `gluedFun_eventuallyEq`** (proven,
for H⁰ surjectivity of *functions*) — the inverse needs only the *form* analogue
(`ω.toFun x := (∂̄η_{idx x})(x)`, smooth because it locally `= ∂̄η_i` on each `U_i`, i-independent by
the cocycle). This is NOT novel infra.

**The double-sum below is RECORDED but DEPRECATED.** `ω = ∑_{j,k} ρ_j(∂̄ρ_k)f_jk` is the Čech–de Rham
double-complex "collating formula" (Bott–Tu §8–9, de Rham case) — correct and equivalent, but it is a
reorganization chosen to dodge the section-gluing, and it is *not* the route the project's reference
(Forster) takes. Per the user's directive (no non-canonical shortcuts), prefer the gluing route. Keep
the double-sum only as a fallback if the form-gluing proves intractable in Lean.

## ⭐ (RECORDED, DEPRECATED) Double-sum construction

**Avoid the per-point gluing entirely.** Build `ω` as a *finite sum of global smooth forms*:

`ω := ∑_{(j,k)} ρ_j · (∂̄ρ_k) · F_{jk}`   (`F_{jk}` = holomorphic rep of `f_{jk}`).

Each term `T_{jk} := ρ_j · (∂̄ρ_k) · F_{jk}` is **global smooth**: it is supported in `U_j ∩ U_k`
(`ρ_j` vanishes off `U_j`, `∂̄ρ_k` off `U_k`), so it extends by `0` to all of `X`. Verified that
`ω|_{U_i} = ∑_k (∂̄ρ_k)·f_ik = ±∂̄(local primitive)` via the cocycle (`f_jk = f_ik − f_ij` on triples,
`∑ρ_j = 1`, `∑∂̄ρ_k = ∂̄1 = 0`) — so `[ω]` is the right Dolbeault class.

**Infra that makes this work (all confirmed present):**
- `ContMDiff.smul_section` / `ContMDiffOn.smul_section_of_tsupport`
  (`…/VectorBundle/SmoothSection.lean`): smooth/`tsupport`-localized scaling of sections — builds
  `T_{jk} = ρ_j • (F̃_{jk} • ∂̄ρ_k)` as a genuine `SmoothCOneForms` (no by-hand section).
- `SmoothCOneForms` is a `Module ℝ`; the fiber `ℂ →L[ℝ] ℂ` is a `ℂ`-module (scale by `F̃_{jk} : X→ℂ`).
- `∂̄ρ_k := dbarL ρ̃_k` where `ρ̃_k = ofReal ∘ ρ_k : SmoothCFunctions` (the only coe to watch).
- `F̃_{jk} = Gext (holoRep f_jk)` (phase-2 `holoRep` + `Gext`), smooth on `U_j∩U_k`.

**Linearity in `f` (no identity theorem needed):** `holoRep` uses choice, but two reps of the same
class differ by a *codiscrete-zero* function; multiplied by the smooth `ρ_j·∂̄ρ_k` the difference is a
*continuous form vanishing off a dense (codiscrete-complement) set* ⟹ `0`. So `ω(f₁+f₂) = ω(f₁)+ω(f₂)`
and `ω(c•f) = c•ω(f)` hold at the form level. (`Filter.codiscreteWithin` complement is dense.)

**Membership `ω ∈ OneFormsZeroOne`:** each `T_{jk}` is `(function) • (∂̄ρ_k)`, and `∂̄ρ_k ∈
OneFormsZeroOne` (`dbarL_mem_zeroOne`); `OneFormsZeroOne` is closed under the fiber `ℂ`-scaling
(it is `range proj01L`, and `proj01` commutes with codomain scaling) — small lemma.

This is **far more tractable** than Route G (no `gluedFun`-for-forms, no `idx`, no `eventuallyEq`
smoothness). Revised phase order: ②`holoRep` ✅ → ③ `ρ̃`/`∂̄ρ` + the `T_{jk}` term → ④ `ω` = finite
sum, membership, linearity → ⑤ well-definedness → ⑥ round-trips.

## (Superseded) Route G: building `ω` as a global `ContMDiffSection`

`SmoothCOneForms = ContMDiffSection …`; a section is `{ toFun, contMDiff_toFun }`. Two viable routes:

* **Route G (gluedFun-for-forms, recommended).** Mirror `CechH0.gluedFun`: pick an index function
  `idx : X → ι` with `x ∈ U_{idx x}`, set `ω.toFun x := (∂̄η_{idx x})(x)` (the local form value).
  Prove `contMDiff_toFun` by: near `x₀`, `ω =ᶠ ∂̄η_{i₀}` for `i₀ = idx x₀` (the value is
  i-independent on `U_{i₀}∩U_{idx ·}`, by the cocycle), and `∂̄η_{i₀}` is smooth on `U_{i₀}` — so
  `ω` is smooth at `x₀`. This reuses the `gluedFun_eventuallyEq` proof pattern (already done for
  functions) at the section/fiber level.
  - Requires `η_i` as a **global** `SmoothCFunctions X` agreeing with `∑_k ρ_k·f_ik` on `U_i`
    (so `∂̄η_i = dbarL η_i` is a genuine `SmoothCOneForms`), OR a submanifold `∂̄`. The global-lift
    `exists_smoothLift_of_chartFun` pattern + PoU `finsum_smul` should produce a global `η_i` smooth
    everywhere and `= ∑_k ρ_k·f_ik` near each point of `U_i`.

* **Route S (build the section-gluing lemma).** A standalone `exists_glued_section`: given an open
  cover, local `ContMDiffSection`s agreeing on overlaps, produce a global one. More reusable but more
  upfront infra; no Mathlib base.

Route G is preferred (reuses the proven `gluedFun` template; no new general API).

## Build phases

1. **Structural `liftQ` decomposition** (small, mirrors forward commit `ada8b7e`): replace the bare
   `cech_to_dolbeault` sorry with `Submodule.liftQ` of `mkQ_{im∂̄} ∘ cechToDolbeaultForm`, isolating
   - `cechToDolbeaultForm : ↥(cocycles1 0) →ₗ[ℝ] ↥(OneFormsZeroOne X)` (analytic kernel, sorry), and
   - `cechToDolbeaultForm_coboundary_le` (well-definedness, sorry).
   Assembly sorry-free. **Do first.**
2. **Holomorphic-rep lemma**: `OmegaDGerm 0`-class ↦ its unique holomorphic function rep (+ that its
   `∂̄` read in charts vanishes). Small.
3. **Local primitive `η_i`** (global smooth, `= ∑_k ρ_k·f_ik` near `U_i`) via PoU `finsum_smul` +
   the global-lift pattern. Medium.
4. **`cechToDolbeaultForm`** = `[f] ↦ ω` via Route G (the gluedFun-for-forms section). The core; the
   smoothness/gluing is the hard part (~150 LoC, adapts `gluedFun_eventuallyEq`).
5. **`cechToDolbeaultForm_coboundary_le`**: a coboundary `f = δ⁰{s_i}` (`s_i` holomorphic) ⟹ `ω = ∂̄`
   of the glued global primitive ⟹ `[ω] = 0`. Medium (reuses gluing).
6. **Round-trips** `*_comp_* = id`: the hardest — need both constructions explicit and a Čech-level
   computation (`dolbeault∘cech`) and a Dolbeault-level one (`cech∘dolbeault`). Reuse the forward
   `rawCochain`/`diskSection` + the inverse `η_i`. Largest risk.

## Scale / risk

Comparable to the forward direction (~400–600 LoC). The genuinely new, no-Mathlib-base piece is the
**form gluing** (phase 4) — mitigated by adapting the proven `CechH0.gluedFun` template. Phases 1–3
are low risk; phase 4 medium-high; phase 6 (round-trips) highest. Bijectivity-via-finrank is NOT a
shortcut (it would still need the gluing for injectivity/surjectivity, and the finrank equality
currently depends on the very iso we are building).

## Recommended order

Phase 1 now (clean, committable). Then 2→3→4→5 (the construction), then 6 (round-trips). Each phase
its own commit; isolate any residual hard step as a named honest sorry (per the file's methodology).

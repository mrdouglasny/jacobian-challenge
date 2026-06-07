# Dolbeault wall — concrete keystone decomposition of the ∂̄-on-a-disk atom

> **UPDATE 2026-06-01 (later):** G1 disk atom is ~done (the polar Cauchy–Pompeiu route worked,
> roughly on-estimate). **CORRECTION:** the G3 compactness engine `Montel.closedBall_isCompact` is
> **PROVEN in-repo** (`Montel.lean` is 0-sorry), *not* a sorry as stated below — so G3 is "adapt a
> proven normal-families technique to the Čech-H¹ cochains," not greenfield. The concentrated
> remaining GREENFIELD risk is **G4 (𝒪_D-on-a-manifold + Serre duality)**. Ladder + frontier: `docs/STATUS.md`.


Read-only research note for `/home/rado/jacobian`, 2026-06-01. Decomposes the **one
thing the prior RR/Dolbeault docs hand-waved**: the actual keystone ladder of the Dolbeault
∂̄-solvability layer, starting from the disk atom (Cauchy transform). Companion to
`docs/riemann_roch_proof_plan.md`, `docs/dolbeault_hodge_feasibility.md`. Pin `8e3c989` /
`v4.30.0-rc1`. Verdicts marked **[VERIFIED]** (grep of `.lake` Mathlib this session) /
**[BOOK]** (Forster §13–17) / **[BELIEVED]** (engineering judgement).

## 0. Bottom line (what's NEW vs the prior docs)

The prior docs scoped Dolbeault as "~3–6k LoC, fully greenfield, ~500-LoC disk atom." Direct
Mathlib grep sharpens this materially:

1. **The disk atom is well-scaffolded, not greenfield.** Three of its four sub-pieces ride
   *existing* Mathlib machinery: convolution-differentiation, the 2D divergence theorem (the
   same one the repo's `GreenBox` already wraps), and the parametric-integral derivative. The
   atom is **~300–500 LoC**, and its genuine mathematical content is a singular-kernel
   divergence computation **in the same family as the repo's already-proven GreenBox/CutSurface
   work** — i.e. the repo has directly transferable skill + prior art.
2. **Globalization is HAVE, not greenfield.** `SmoothPartitionOfUnity.exists_isSubordinate`
   exists and applies to the repo's compact `X` (needs only a free `SigmaCompactSpace` instance
   from `CompactSpace`). Forster's "patch local solutions" step is scaffolded. **[VERIFIED]**
3. **The genuine remaining wall is `H¹` finiteness — but its ENGINE is already proven in-repo.**
   The Montel/Schwartz compactness for the Čech-`H¹` cochains (Forster 14.9) is the new work, BUT
   the repo's global-`Ω(X)` Montel (`HolomorphicOneForms.closedBall_isCompact`, `Montel.lean`) is
   **PROVEN, axiom-clean** (0-sorry; via `exists_convergent_subseq_of_bounded`) — so the
   normal-families/sequential-compactness *technique* is demonstrated; G3 is *adapting* it to the
   cochains, not building it from scratch. **[VERIFIED 2026-06-01]** The `𝒪_D`-sheaf-on-a-manifold
   framing (G4) is the true remaining greenfield pole, not the compactness and not the local ∂̄.

**Net:** the *local* Dolbeault atom + globalization are tractable (~400–600 LoC, mostly riding
Mathlib); the cost and risk concentrate in **(i) `H¹` finiteness (compactness)** and **(ii) the
sheaf-on-a-manifold scaffolding** to even state `H^i(X, 𝒪_D)`. The right first buildable probe
is the disk atom — it is bounded, rides existing machinery, and calibrates the rest.

---

## 1. The disk atom — accurate decomposition

**Target (Forster §13.2):** for `g` continuous (Hölder/`C^k`) on the closed disk `D̄_r`, the
**Cauchy transform** `u(z) := -(1/π) ∬_{D_r} g(ζ)/(ζ-z) dA(ζ)` is `C¹` (`C^{k+α}`) on `D_r` and
solves `∂̄u = g` there. The clean Lean route splits regularity from the solvability identity.

| Step | Content | Mathlib support | Verdict | LoC |
|---|---|---|---|---|
| **D0** | Define `K z := -(1/(π·z))` and prove `LocallyIntegrable K volume` on ℂ≅ℝ² (kernel `1/‖z‖` integrable in 2D: `∫ r·(1/r) dr dθ < ∞`). | Polar-coordinate CoV `Complex.integral_comp_polarCoord_symm`, `lintegral_comp_polarCoord_symm` (`Analysis/SpecialFunctions/PolarCoord.lean`); `integrableOn_Ioi_comp_rpow_iff` (`Integral/IntegralEqImproper.lean`). The isolated "‖x‖⁻¹ loc-integrable on ℝ²" lemma is **ABSENT** — synthesize via polar coords. **[VERIFIED]** | **PARTIAL→buildable** | ~60–100 |
| **D1** | `u := g ⋆ K` for `g ∈ C^∞_c(ℂ)`. Get `u ∈ C^∞` AND `∂̄u = (∂̄g) ⋆ K` — derivative transfers onto the SMOOTH factor, kernel needs only local integrability. | `HasCompactSupport.hasFDerivAt_convolution_left`, `…contDiff_convolution_left` (`Analysis/Calculus/ContDiff/Convolution.lean`): hyp = `HasCompactSupport g`, `ContDiff 𝕜 n g`, `LocallyIntegrable K`. **[VERIFIED]** | **HAVE** | ~60–100 |
| **D2** | **The genuine content — fundamental-solution identity** `(∂̄g) ⋆ K = g` for `g ∈ C^∞_c`. This is Cauchy–Pompeiu with NO boundary term (compact support kills it): `g(z) = -(1/π)∬ ∂̄g(ζ)/(ζ-z) dA`. Proof = apply the 2D divergence theorem to `g(ζ)/(ζ-z)` on the annulus `ε≤|ζ-z|≤R`, the inner circle → `g(z)` as `ε→0` (the `2πi` residue brick), boundary `R` term vanishes by support. | `integral2_divergence_prod_of_hasFDerivAt_off_countable` (`MeasureTheory/Integral/DivergenceTheorem.lean`) — **the same divergence theorem the repo's `GreenBox.greenOnUnitBox` already wraps**; the inner-circle residue limit is the repo's already-used `circleIntegral_sub_center_inv_smul_…_tendsto` (→ `2πi•g(z)`). **[VERIFIED]** | **buildable (repo prior art)** | ~150–250 |
| **D3** | Combine D1+D2: `∂̄u = (∂̄g)⋆K = g` for `g ∈ C^∞_c`. Then for general continuous `g` on a disk: cut off by a bump `χ∈C^∞_c` (=1 near the point), solve for `χg`, the difference `∂̄`-vanishes ⟹ holomorphic correction. | bump functions `ContDiffBump` (`Analysis/Calculus/BumpFunction/`); the holomorphic-correction step is repo-style. **[VERIFIED bumps]** | **buildable** | ~80–150 |

**Disk-atom total: ~350–600 LoC**, dominated by **D2** (the singular-kernel divergence
computation). **Crucial:** D2 is *not* novel greenfield for this repo — `GreenBox`,
`CutSurface`, `rectBoundaryIntegral`, `EdgeChangeOfVariables`, and the `circleIntegral…tendsto`
residue brick are exactly this toolkit. The repo has already proven harder versions (the
boundary-word/period computations). **This is the single most-leveraged buildable probe of the
whole wall** and should be the first concrete step.

**Honest correction to an over-optimistic read:** convolution machinery (D1) gives *regularity
of `u`* and moves `∂̄` onto `g`, but it does **not** by itself prove `∂̄u = g` — that is D2, the
fundamental-solution identity, which is the genuine ~150–250 LoC. Do not conflate "u is smooth"
with "u solves the equation."

---

## 2. From the atom to global `H¹(X,𝒪)` — the ladder, with where it gets hard

| Rung | Content (Forster) | Scaffold | Verdict | LoC |
|---|---|---|---|---|
| **G1** | Disk atom (§1): local `∂̄u=f` solvable on a chart disk. | rides Mathlib (§1) | buildable | 350–600 |
| **G2** | **Globalize:** patch local solutions via a smooth partition of unity subordinate to a finite chart cover ⟹ `∂̄`-solvable up to a smooth global error; iterate. | `SmoothPartitionOfUnity.exists_isSubordinate` (`Geometry/Manifold/PartitionOfUnity.lean`); needs `[SigmaCompactSpace X]` (free from `CompactSpace`). **[VERIFIED]** | **HAVE** | 150–350 |
| **G3** | **`H¹(X,𝒪)` finite-dimensional** (Forster Thm 14.9): the Čech `δ` is "almost surjective" — a **Montel/Schwartz compactness** argument (sup-norm bounded holomorphic cochains have convergent subsequences ⟹ finite cokernel). | Mathlib **Arzelà–Ascoli** (`Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`) + `TendstoLocallyUniformlyOn.differentiableOn` (`Analysis/Complex/LocallyUniformLimit.lean`); repo `Montel/*` is **0-sorry — `closedBall_isCompact` PROVEN** (the engine), only the Čech-cochain adaptation is new. **[VERIFIED 2026-06-01]** | **engine PROVEN; adapt to cochains** | 800–2000 |
| **G4** | **`𝒪_D` / `H^i(X,𝒪_D)` as objects** on a complex manifold (to run the skyscraper SES + `χ`-additivity, which are *elementary given the objects* — Mathlib's snake lemma/LES/`eulerChar` are present). | **ABSENT** — no structure sheaf on a manifold, no `𝒪_D`. The abstract homological toolkit has nothing to apply to. **[VERIFIED]** | **ABSENT — the other long pole** | 1000–2500 |
| **G5** | **Serre duality / residue pairing** `H¹(X,𝒪_D) ≅ H⁰(Ω(−D))^*`. Integral side (sum-of-residues=0) reuses the repo's `boundaryForm`/Green stack; analytic side (perfectness) rests on G1–G3. | repo Green stack for the integral half; analytic half greenfield on G1–G3. **[VERIFIED partial]** | PARTIAL | 1500–3000 |
| **RR** | Assemble `l(D)−l(K−D)=deg D+1−g`. | abstract homological algebra present; gated on G4. | derivation | +500–1500 |

**Reading:** G1+G2 (local solvability + globalization) are the tractable, Mathlib-riding part
(~500–950 LoC). The wall is **G3 (compactness/finiteness)** and **G4 (sheaf-on-a-manifold)** —
the two genuinely unscaffolded multi-k-LoC inputs. Note G3's compactness is the *same kind* of
argument as the repo's own `Montel.closedBall_isCompact` — **finishing that existing repo
`sorry` first is a natural sub-probe** for whether the G3 style is tractable here.

---

## 3. Recommended sequencing (de-risk the wall before committing)

1. **Build the disk atom D0–D3 (§1).** Bounded (~350–600), rides Mathlib + the repo's own
   GreenBox/residue toolkit, and is the fundamental-solution brick every higher rung reuses.
   This is the single best calibration probe: it converts "is Dolbeault 3k or 6k+?" into data.
2. **Finish the existing repo `Montel.closedBall_isCompact` `sorry`** (global-`Ω(X)` Montel) —
   a smaller, already-scaffolded instance of the G3 compactness style; tells us whether the
   finiteness argument formalizes cleanly before committing to Čech-cochain Montel.
3. **Only then** decide G4 (sheaf-on-manifold) vs. the specialized routes (the prior docs'
   Path 2: ℂℙ¹-shim + isolated-RR for #1, Radó for #7, isolate-Abel for #3). G3+G4 are where
   the project would commit 2–5k LoC; do not start them blind.

**One-line:** the local Dolbeault machinery is far more Mathlib-supported than the prior docs
assumed (convolution + divergence theorem + partition of unity all present); the irreducible
cost is `H¹` finiteness (G3) and the `𝒪_D`-on-a-manifold scaffolding (G4). Build the disk atom
first as the load-bearing brick + cost probe.

## 4. Sources
- **Forster, *Lectures on Riemann Surfaces* (GTM 81)** §13 (Dolbeault local solvability /
  Cauchy transform), §14 (finiteness Thm 14.9), §16 (RR), §17 (Serre). **[BOOK]**
- **Mathlib [VERIFIED this session, pin `8e3c989`]:**
  `Analysis/Calculus/ContDiff/Convolution.lean` (`HasCompactSupport.hasFDerivAt_convolution_left/right`,
  `…contDiff_convolution_*`); `MeasureTheory/Integral/DivergenceTheorem.lean`
  (`integral2_divergence_prod_of_hasFDerivAt_off_countable`); `Analysis/Complex/CauchyIntegral.lean`
  (`two_pi_I_inv_smul_circleIntegral_sub_inv_smul_…`, `circleIntegral_…_tendsto`);
  `Analysis/SpecialFunctions/PolarCoord.lean`; `Analysis/Calculus/ParametricIntegral.lean`
  (`hasFDerivAt_integral_of_dominated_loc_of_lip`); `Geometry/Manifold/PartitionOfUnity.lean`
  (`SmoothPartitionOfUnity.exists_isSubordinate`); `Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`;
  `Analysis/Complex/LocallyUniformLimit.lean`. **ABSENT:** Cauchy–Pompeiu, Dolbeault, `𝒪_D`/
  structure-sheaf-on-manifold, Serre, RR, finiteness-of-cohomology.
- **Repo:** `Jacobians/DbarDisk.lean` (only the trivial `dbar_eq_zero_of_differentiableAt`
  direction so far — solvability NOT started); `Jacobians/GreenBox.lean`, `CutSurface*.lean`,
  `EdgeChangeOfVariables.lean` (the divergence/boundary toolkit D2 reuses);
  `Jacobians/Montel*.lean` (`closedBall_isCompact` still `sorry` — the G3 sub-probe).

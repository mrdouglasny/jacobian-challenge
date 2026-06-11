# DICT_ROUTE — the Čech↔tail dictionary (`CechTailComparison`), route decision

Branch `feat/cech-tail-dictionary`, 2026-06-11.  Target: prove
`CechTailComparison 𝔇 g G D` (`TailUnwind.lean`) for the concrete fine-sheaf
`G = (cousinResidueData_of_witnessR hsep g hg … hwit).toGlobalResidue`, all `D`.

## 0. Inventory verdicts (what the route options actually look like)

### The dictionary is EQUIVALENT to isolation-free `UnwindRegularity` — not weaker

Given the slot frame (`SlotExactK 𝔇 g K`, `K ≥ 0`), for ANY `G`:

* `CechTailComparison 𝔇 g G D ⟹ UnwindRegularity G D` — proven
  (`unwindRegularity_of_cechTailComparison`, rung 4).
* `UnwindRegularity G D ⟹ CechTailComparison 𝔇 g G D` — NEW, easy: the
  factorization upgrades `fE` to the `L(K−D)` order bounds
  (`exists_lSysInclMono_eq_iff`), then EVERY gap coefficient `m < D b` sits strictly
  below the slot-product order `orderW fE b + K b ≥ D b`, so it vanishes by the kernel
  law (`laurentCoeff_eq_zero_iff`).  Formalized as
  `cechTailComparison_of_unwindRegularity` (`TailDictionary.lean`).

So the keystone residual is EXACTLY: `UnwindRegularity G D` for the concrete `G`
without the `BadPointsIsolated` discipline — i.e. the §17.7 detection at a forced bad
point `b` that may lie in several cover sets.  No tail-frame-native shortcut exists:
route (c) cannot evade the detection because the leading-coefficient case of the gap
window is `tailCoeff_leading_ne_zero` (automatically NONZERO), so the hypothesis
`hfac` must be *contradicted* there — that contradiction is the residue evaluation.

### Route (b) — cover refinement: REJECTED

To use the proven isolated case on a refined cover `𝔙` one needs all three of
(i) a refined `ChartDiskCover` carrying the full R-lane data with `b` isolated,
(ii) the residue-functional refinement compatibility `res_𝔙 ∘ refineH1 = res_𝔇`
(an integral statement comparing two PoU presentations — as hard as the direct
evaluation), and (iii) surjectivity of `refineH1` at level `E` to transport the
factorization (only conditional on `RefinementLift`/overlap disk-acyclicity —
`CechRefinementLeray.refineH1_surjective_iff_lift`; the contravariant trick does NOT
dodge it: the skyscraper test class on `𝔙` must be hit from `𝔇`, and
`refineH1_injective_unconditional` only helps AFTER a preimage exists).  Three
substantial open ingredients vs. route (a)'s one.  Rejected.

### Route (a) — multi-chart evaluation: CHOSEN, and it is MUCH cheaper than
`UNWIND_BLOCKER.md` estimated.  Three discoveries:

**(D1) Wall 1 is vacuous.**  The R0 atom `integral_dbar_smearedSimplePole`
(`SignTest.lean:104`) is ALREADY the general Cauchy–Pompeiu statement
`∫ ∂̄(χ·(ζ−a)⁻¹) = −π·χ(a)` for ANY smooth compactly supported `χ` — no local
constancy near `a` is required.  The marked engine used `eventuallyEq_pouCoeff_one_near_iso`
only to make the repaired remainder smooth, not because the atom needs it.

**(D2) `K b = 0` at every non-isolated point.**  `SeparatesPoles 𝔇 K` forces
`K x ≤ 0` on every overlap of distinct cover sets; with `K ≥ 0` (`hKeff`) every
non-isolated point has `K b = 0` (`K_apply_eq_zero_of_not_isolated`,
`TailDictionary.lean`).  So in the residual case the `dz`-slot is a UNIT at `b`
(`SlotExactK`, `(K b).toNat = 0`) and the marked excess is a clean SIMPLE pole — no
order-`m` ladder, no higher Cauchy–Pompeiu.

**(D3) The global-cutoff subtraction kills the multi-chart smearing.**  The marked
point `b` lies in the star `{i : b ∈ U i}`.  The cup 0-cochain `c⁰ := fE·n̂` (with the
DEEP-matching skyscraper `n̂`, see W2) has the same simple pole at `b` in every star
chart, with MATCHING principal parts (that is what level-`E` membership of `δ⁰c⁰` on
overlaps containing `b` means).  Let `θ` be a smooth cutoff `≡ 1` near `b`, supported
in a small disk inside `U j₀` avoiding all other bad points, and set the GLOBAL
function `H := θ·c⁰_{j₀}` (extended by `0`).  The constant 0-cochain `(H,…,H)` has
`δ⁰ = 0`, so

  `δ⁰(c⁰) = δ⁰(h̃)`,  `h̃_i := c⁰_i − H`.

The presentation `h̃` has NO bad point at `b` at all: near `b`, `h̃_i = c⁰_i − c⁰_{j₀}`
extends analytically (matching parts + `ord fE = n ≥ E b`, gap index `m = n`,
`K b = 0` ⟹ `ord ≥ n − E b ≥ 0`).  Its only bad points are the cover-isolated
K-points.  The price: `h̃` is smooth but NOT holomorphic on the annulus
`{dθ ≠ 0}` — with the COMMON discrepancy `∂̄h̃_i = −∂̄H` (independent of `i`).

Consequences for the engine (`resFunctional_eq_neg_residue_of_mero_coboundary`'s
skeleton, `MeroVanish.lean`):

* the curvature relocation + reinsertion kill steps consume only `hsm` (smoothness
  off the isolated bad set) — UNCHANGED;
* the per-chart Stokes term `∫ ∂̄(ρ̃_j·β̃·g̃)` now DIES for every chart (vanish-engine
  style, `SlotProductExtendsAt` at the K-points; `β̃·g̃` is smooth at `b`'s
  coordinates) — the marked-chart evaluation DISAPPEARS;
* the Leibniz split gains ONE new explicit term per chart,
  `−∫ ρ̃_j·(∂̄H-read_j)·g̃_j` (this is the only place `hhol` was consumed);
* the new terms collapse by the R4 relocation lemma (weight `ρ_j`) + `∑ρ ≡ 1` to a
  SINGLE chart-`j₀` integral `−∫ ∂̄(H̃·g̃_{j₀})` — evaluated by (D1):
  `∫∂̄(θ̃·F) = −π·r·θ̃(α) = −π·r` where `F = (c⁰_{j₀})read·g_{j₀}` has the simple-pole
  shape `r·(ζ−α)⁻¹ + analytic` (`SlotProductSimplePoleAt`, supplied by the EXISTING
  `exists_slotProductSimplePoleAt`, which never used isolation).

Net: `resFunctional = resNormalization·(π r) = −r ≠ 0` — the same conclusion as the
isolated marked engine, with **no cross-chart residue transport** (wall 2 vanishes:
only chart `j₀`'s read is ever evaluated) and **no per-chart partial weights** (wall 3's
telescoping is replaced by the relocation collapse).

## 1. Work plan (route a, global-cutoff form)

| # | Piece | Status |
|---|-------|--------|
| W0 | `TailDictionary.lean`: `cechTailComparison_of_unwindRegularity` (the reduction; with rung 4 this is the formal EQUIVALENCE), `K_apply_eq_zero_of_not_isolated` (D2), per-instance corollary `cechTailComparison_concrete_of_isolated` | this branch |
| W1 | The common-discrepancy evaluation engine in `MeroVanish.lean`: modified Leibniz split (`∂̄h̃ = −∂̄H` replaces `∂̄h = 0`), the `(1,1)` family `∂̄H̃·g̃` + relocation collapse to chart `j₀`, final (D1) atom evaluation; headline `resFunctional_eq_neg_residue_of_global_correction` | this branch (partial → DICT_BLOCKER) |
| W2 | Deep-matching skyscraper: per star chart `U i ∋ b`, a section `c_i ∈ 𝒪_{Ě+b}(U i)` whose FULL window tail at `b` (orders `−(m+1) … −(E b+1)`, ambient chart) matches a prescribed target — triangular induction on the window over `ExactOrderWitness`; then `δ⁰c ∈ Z¹(𝒪_E)`, trivialized at level `D` by `c` itself.  (The single-coefficient cone `coneB0` only gives level-`Ě`; insufficient for `m > E b`.) | open |
| W3 | The X-side cutoff `θ` (planar bump through chart `j₀`, `pouCoeff`-style two-open smoothness argument) + the one-point repair of `h̃` at `b` | open |
| W4 | Pairing-side bookkeeping: `h̃ := vanishFn(c⁰) − θ·vanishFn(c⁰)_{j₀}` honest presentation, `IsCoboundaryOn` at the repaired point, `SlotProductExtendsAt` inheritance at unmarked K-points | open |
| W5 | Assembly: `unwindRegularity_concrete` (no isolation: forced bad point, case split on `∃ j₀, MLIsolated` via existing isolated theorem / new engine), then `cechTailComparison_concrete` via W0 | open |

Estimated remaining (W1–W5): ~1.3–1.7k LoC of pattern-following Lean on top of the
existing engine; the analytically novel content is ZERO (every integral step is an
existing atom).

## 2. Honest strength notes

* `CechTailComparison` for the concrete `G` is NOT yet a theorem for all `D`; it is
  now formally pinched between two proven implications
  (⟸ `UnwindRegularity`, ⟹ `UnwindRegularity`), with the open core exactly the
  isolation-free detection, and the route to it de-risked as above.
* For any `D` with `BadPointsIsolated 𝔇 K D` (in particular every per-instance use
  where the violating point is isolated), `CechTailComparison` IS a theorem
  (`cechTailComparison_concrete_of_isolated`).

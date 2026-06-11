# TAILRR_BLOCKER — residual inputs of the tail Riemann–Roch tower

Branch `feat/tail-riemann-roch` (on the #184 tower). Route: `docs/planning/TAILRR_ROUTE.md`.
Updated 2026-06-11.

## What is PROVEN (standard-3 `#print axioms`-verified, zero custom axioms, zero sorries)

| Rung | File | Content |
|------|------|---------|
| T1 | `TailCoeffFull.lean` | FULL Laurent coefficients by leading-term stripping over the proven `laurentCoeff`: `stripFun`/`fullCoeffFrom` (meromorphy, strip order law, honest reads, level irrelevance) and the X-level `coeffAt` (full linearity with NO order hypotheses, order law iff, leading-coefficient nonvanishing, germ-junk invariance, `tailCoeff` compatibility). |
| T2–T3 | `TailSpaceGlobal.lean` | Global truncated-tail space `𝒯[D] ⊆ (X×ℤ) →₀ ℂ`, upper space `𝒰[D]`, truncation `truncTails` (linear, identity on target, composition law), window space with `dim 𝒲(D,D') = deg D' − deg D` (+ instance-clean Pi model `WindowModel`), and the tail map `α_D` (coefficient law, linearity, `ker α_D = L(D)`, junk invariance, level compatibility). |
| T4 | `TailRR1.lean` | `H1Tail D := GlobalTails ⧸ (im α_D ⊔ 𝒰[D])` with surjective monotone connecting maps; the window exactness identities; **finiteness `h¹_t(D) < ∞`** (deep-truncation kill + Riemann-inequality M-bound — no Čech vanishing, no duality); **tail Riemann–Roch I** `l(D) − h¹_t(D) = deg D + 1 − tailGenus X` for EVERY divisor (`tail_riemannRoch_I`). |
| T5 (A–D) | `TailSerre.lean` | `planarCoeff` (planar full coefficients), the **window product law** `resCoeff_mul_window`, the pair frame `TailPairFrame` (slots + the residue-theorem atom as a field), the **residue pairing** `pairingL : L(K−D)/junk →ₗ Dual(H¹_t(D))` (well-defined = W1 upper-kill + W2 residue descent), and the **injectivity half**: `pairingL_injective`, `lDim (K−D) ≤ h1TailDim D`. |
| T5 (E) | `TailSerre.lean` | Under `PairingSurjective`: full tail Serre duality `h¹_t(D) = l(K−D)`, `g_t = l(K) = kirovGenus` (via `hKgenus` + `FormRemovableSingularity`), `deg K = 2g_t − 2`, and **`tailRiemannRoch_of_pairingSurjective : TailRiemannRoch X`** — the `TailGenusTarget.lean` named input, verbatim — plus the keystone-facing `h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame`. |

Headline (verbatim):

```lean
theorem TailPairFrame.tailRiemannRoch_of_pairingSurjective
    (P : TailPairFrame X) (hs : P.PairingSurjective) : TailRiemannRoch X
```

So `TailRiemannRoch X` is now a theorem **conditional on exactly two named inputs**, both
hypotheses (no axioms introduced):

## Residual input 1 — `Nonempty (TailPairFrame X)` (frame construction)

**STATUS (2026-06-11, F-lane): DISCHARGED at positive genus — sorry-free, axiom-free.**
`TailFrameWitness.lean`: `nonempty_tailPairFrame_of_kirovGenus_pos : 0 < kirovGenus X →
Nonempty (TailPairFrame X)` (kernel standard-3). The atom `∑Res(F·ω₀) = 0` was NOT new
analysis: with `ω₀ := holToMero α` for a nonzero holomorphic `α` (exists iff genus > 0),
it is the PROVEN Gate-A `residueTheorem_unconditional`, transported by two new bridges —
`resAt_eq_planarCoeff_neg_one` (contour residue = planar `c₋₁`, leading-monomial stripping)
and `MeromorphicFunction.repair` (holoRepr junk repair giving the honest-analyticity
hypothesis). Genus 0 is intentionally out of scope (no nonzero holomorphic frame form).

```
structure TailPairFrame where
  data : CanonicalForm17Data X            -- PROVEN nonempty (nonempty_canonicalForm17Data)
  slot : (p : X) → ℂ → ℂ                  -- chart reads of ω₀'s dz-coefficient
  slot_mero / slot_order                  -- meromorphic, exact order K p
  resSum : ∀ F, ∑_{p ∈ supp(div F) ∪ supp K} Res_p(F·ω₀) = 0   -- THE analytic atom
```

Two sub-pieces:
1. **Slots from `ω₀`** (routine): the chart-coefficient reads of `data.ω₀` at each `p`,
   with meromorphy and exact order `K p` — the `formCoeff`/`exists_form_divisor` API of
   `CanonicalFormIso.lean`/`CanonicalFormDifferential.lean` already carries this content
   (`formOrderW ω₀ p = K p` is `data.hK`); the work is the chart-read normal form. Days.
2. **The pair-frame residue theorem `∑Res(F·ω₀) = 0`** (the genuinely analytic atom):
   Port status: `FormResidueTheorem.lean` has the trace-route skeleton with the trace
   CONSTRUCTION open (Gate A; the `FormTrace*` family is conditional); Kirov's own tree
   discharges it via the Stokes-atom tower (`ResidueTheoremStokes`, ~3.7k LoC, post-base —
   route ideas only, `KIROV_ROUTE_IDEAS.md` item 4). Shared infrastructure with Abel-⊆
   (item 1's E3b). **This is the single analytic blocker of the whole lane.**

## Residual input 2 — `P.PairingSurjective` (the Miranda VI.3.10 surjectivity half)

```
∀ D, Function.Surjective (P.pairingL D)   -- L(K−D)/junk ↠ Dual(H¹_t(D))
```

Recovery + growth pigeonhole: the `ℳ(X)`-module action on tail functionals (the W1/W2
multiplication–truncation identities — the `resCoeff_mul_window` engine already covers the
product-coefficient algebra), `serre_surjectivity_dim_core` (proven, `SerreDuality.lean`)
for the dimension count over `tail_riemannRoch_I` (proven), and the rung-2 regularity
(`TailRegularity.lean`, proven) for the division step. All shapes exist; this is sustained
bookkeeping, NOT new analysis. Estimated 1–2 weeks of lane time (Kirov actuals:
`PairDualitySurjective.lean` ≈ 700 LoC).

## Downstream readiness (checked this session)

* `TailGenusTarget` consumes `TailRiemannRoch X` directly: with inputs 1+2,
  `h1Dim_zero_chartDiskCover_eq_kirovGenus` etc. all fire
  (`h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame` instantiates it).
* **Layer-3 flip of `h1coh_zero_finrank`** (main repo, `Jacobians/Layer3/Cohomology.lean`):
  fully wired —
  `finrank (H1coh 0) = h1Dim 0` (`FreeAbelianGroup.equivFinsupp` `map_zero`),
  `h1Dim 0 = kirovGenus X` (the tower output), and
  `kirovGenus X = genus X` via the EXISTING bridge
  `Jacobians.Bridge.bridgeKDFormEquiv : HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForms X`
  (`KirovDolbeaultTrace.lean`) + `LinearEquiv.finrank_eq`. No new bridge lemma needed.

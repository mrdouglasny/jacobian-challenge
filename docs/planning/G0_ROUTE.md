# G0 route decision — the genus-0 keystone leg (owner-approved route (i))

*2026-06-10, branch `feat/keystone-g0-leg`, building on the #170 A-lane spine
(`SerreAssemblyPrep.exists_serreDualityData_genus_split`, target interface = its `hzero`
hypothesis `kirovGenus X = 0 → Nonempty (SerreDualityData 𝔘)`).*

## Inventory findings (what the port supplies / does not supply)

| Candidate ingredient | Status | Notes |
|---|---|---|
| `cohomological_riemannRoch` (`CohomologicalRR.lean:216`) | PROVEN from `hR` | `(h0Dim D : ℤ) − h1Dim D = deg D + 1 − h1Dim 0`. RHS genus is the **arithmetic** genus `h1Dim 0`, not `kirovGenus`. |
| `exists_skyscraperLES` (`CohomologicalRR.lean:156`) | PROVEN from `hR` | gives `surj₄ : Surjective (h1Map D P)` ⟹ `h1Dim (D+P) ≤ h1Dim D` (h¹ monotone non-increasing). |
| `h0Dim_eq_lDim` + `globalSectionsEquivQuot` (`CechH0.lean`) | PROVEN | linear equiv `lSysModule D ≃ₗ globalSections D`; transports `finiteDimensional_globalSections_instance` to `lSysModule`. |
| `lDim_eq_zero_of_deg_neg`, `lDim_zero_eq_one` | PROVEN (via `deg_div`, axiom-clean degree route) | |
| `finiteDimensional_cechH1_wired` | PROVEN | |
| `arithmeticGenus_eq_genus` (`DolbeaultLadder.lean:56`) | **keystone-gated** (`exists_serreDualityData` sorry) | circular — FORBIDDEN here. |
| `SerreResidueDirectGenus0*` capstones | target-side only | confirmed (A_LANE_BLOCKER): parametrized by holomorphic `ω₀`, vacuous at source genus 0; supply no realization/pairing. |
| `pairing_injective` (§17.6, `SerreResiduePairing`) | needs a `SerreResidueRealization` | no genus-0 realization constructible from landed artifacts (lane R unlanded even at g ≥ 1). |
| meromorphic `∑Res = 0` at g = 0 | NO Lean artifact | the missing analytic atom named in `A_LANE_BLOCKER.md`. |
| any `h1Dim 0 = 0`-type vanishing | NONE | grep over the port: no unconditional Čech-H¹ vanishing for abstract genus-0 `X` (the `Subsingleton (cechH1 …)` lemmas are disk/refinement-local). |

## Key structural observation (what makes the leg cheap)

`SerreDualityData` constrains its fields only **dimensionally**: `K` need NOT be the order
divisor of a meromorphic form — any divisor with `lDim K = kirovGenus X` works, and `ι D` need
only be SOME bijective linear map `L(K−D) → (H¹(𝒪_D))*`. At `g = 0` take

* `K := Finsupp.single P (−2)` (`deg K = −2 < 0` ⟹ `lDim K = 0 = kirovGenus X` by
  `lDim_eq_zero_of_deg_neg` — no canonical form, no `CanonicalForm17Data` needed);
* `ι D` := an abstract linear equivalence from `finrank` equality
  (`FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`), honest because in finite dimension
  a bijective linear map exists **iff** the dimensions agree — and the dimension equality
  `h1Dim D = lDim (K−D)` is exactly the mathematical content of the field triple
  (`ι`, `ι_inj`, `ι_surj`) as consumed downstream (`serre_eq`).

The dimension equality at `g = 0`, `K = −2P`, splits on `deg D`:

* `deg D ≥ −1`: `h1Dim D = 0` (h¹-monotonicity down to a degree-(−1) divisor, where RR +
  `h0 = l = 0` + **`h1Dim 0 = 0`** give vanishing); `lDim (K−D) = 0` since `deg (K−D) ≤ −1 < 0`.
* `deg D ≤ −2`: `h1Dim D = −deg D − 1` (RR, `h0 = 0`); `lDim (K−D) = deg (K−D) + 1 = −deg D − 1`
  (RR at `K−D` + the same `h¹`-vanishing since `deg (K−D) ≥ 0`).

## The route chosen

**Reduction to a single scalar atom.** Everything above is provable TODAY except ONE input:

```
hga : 𝔘.h1Dim 0 = 0        -- arithmetic genus 0, i.e. Ȟ¹(𝔘, 𝒪) = 0
```

`SerreDualityGenus0.lean` proves (sorry-free, axiom-clean):

* `h1Dim_add_single_le` / `h1Dim_add_nsmul_le` — h¹ monotonicity from the skyscraper LES;
* `h1Dim_eq_zero_of_genus0` — `h1Dim D = 0` for `deg D ≥ −1` given `hga`;
* `exists_serreDualityData_of_arithmeticGenus_zero` — **the g = 0 leg**:
  `hR → kirovGenus X = 0 → h1Dim 0 = 0 → Nonempty (SerreDualityData 𝔘)`;
* `exists_serreDualityData_genus_split_arithmetic` — the spine's split with `hzero` weakened
  to the scalar atom.

`hga` is a NAMED HYPOTHESIS (never a sorry), exactly parallel to the spine's R-lane-gated
inputs. It is also **minimal**: any `SerreDualityData` forces `h1Dim 0 = kirovGenus X`
(`SerreDualityData.arithmeticGenus`), so the g = 0 leg is mathematically EQUIVALENT to `hga`
— no weaker honest interface exists.

## Why not the alternatives

1. **Meromorphic-`ω₀` `GlobalResidue` (blocker shape 1).** Requires the un-landed R6/R7 lane-R
   machinery PLUS the new meromorphic `∑Res = 0` atom — strictly more work than at `g ≥ 1`,
   where lane R is itself still open. Research-grade; rejected as "cheapest path".
2. **Transport from ℙ¹.** `genus_eq_zero_iff_homeo`'s forward direction consumes
   `exists_riemannRoch_divisor` → the keystone sorry: circular. The sphere-side artifacts
   give a homeomorphism (not biholomorphism) anyway, and only target-side residue data.
3. **Zero pairing.** Fails: for `deg D ≤ −2`, `h1Dim D = −deg D − 1 > 0` at `g = 0`, so the
   zero map is not surjective; the structure quantifies over ALL `D`.

## Remaining gap (the honest open atom)

`hga : 𝔘.h1Dim 0 = 0` at `kirovGenus X = 0` — "a compact RS with no holomorphic 1-forms has
vanishing (Čech) H¹(𝒪)". PDE-free routes: (a) the lane-R fine-sheaf functional generalized to
meromorphic `ω₀'` (the A_LANE_BLOCKER atom — then the full data follows and `hga` drops out);
(b) Dolbeault comparison + a `H^{0,1} = 0` argument at genus 0. Both research-grade; tracked
in `G0_BLOCKER.md`.

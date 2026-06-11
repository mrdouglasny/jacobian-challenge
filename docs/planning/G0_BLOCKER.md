# G0 blocker — the residual atom of the genus-0 keystone leg

*2026-06-10, branch `feat/keystone-g0-leg`. Companion to `G0_ROUTE.md` (route decision) and
`SerreDualityGenus0.lean` (the landed reduction).*

## What landed (sorry-free, standard-3 axiom-clean)

`KirovDolbeault/Dolbeault/SerreDualityGenus0.lean` closes the `g = 0` keystone leg down to ONE
scalar input. Headline:

```
exists_serreDualityData_of_arithmeticGenus_zero (𝔘) (hR : 𝔘.LocallyRealizable)
    (hg0 : kirovGenus X = 0) (hga : 𝔘.h1Dim 0 = 0) : Nonempty (SerreDualityData 𝔘)
```

plus `exists_serreDualityData_genus_split_arithmetic`, the lane-A spine's genus split with the
abstract `hzero` leg replaced by `kirovGenus X = 0 → 𝔘.h1Dim 0 = 0`. All seven new
declarations: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`exists_serreDualityData` in the dependency cone.

## The residual atom (research-grade — do NOT fake)

```
hga : 𝔘.h1Dim 0 = 0          -- given kirovGenus X = 0, hR (and hL if needed)
```

i.e. **Čech `H¹(𝔘, 𝒪) = 0` on a compact Riemann surface with no nonzero holomorphic
1-forms.** This is the genuine analytic content of the `g = 0` leg, and it is *minimal*: any
`SerreDualityData 𝔘` forces `h1Dim 0 = kirovGenus X` (`SerreDualityData.arithmeticGenus`), so
no weaker honest interface exists.

Why it is research-grade today:

* `arithmeticGenus_eq_genus` is keystone-gated (proved FROM `exists_serreDualityData`) —
  circular.
* The §17.6 injectivity half gives only `kirovGenus ≤ h1Dim 0` (wrong direction; trivial at
  `g = 0`).
* The §17.9 surjectivity count needs a `GlobalResidue`/realization, which at source genus 0
  requires a residue functional over a MEROMORPHIC `ω₀'` — the exact missing analytic atom
  recorded in `A_LANE_BLOCKER.md` (lane R is un-landed even at `g ≥ 1`).
* The sphere route (`genus_eq_zero_iff_homeo` forward) consumes `exists_riemannRoch_divisor`
  → the keystone sorry: circular; and yields only a homeomorphism, not a biholomorphism.
* No unconditional Čech-H¹ vanishing for abstract genus-0 `X` exists in the port (the
  `Subsingleton (cechH1 …)` artifacts are disk/refinement-local).

## Plausible discharge shapes (for lane R / a future mini-lane)

1. **Meromorphic-`ω₀'` residue functional** (blocker shape 1): once lane R lands
   `CousinResidueData` machinery for a germ-nonzero meromorphic `ω₀'` (`∑Res = 0` at `g = 0`
   via trace-to-ℙ¹ for a degree-`d` map, where every meromorphic form is rational-in-`f`·`df`),
   the FULL `g = 0` data follows through
   `exists_serreDualityData_of_globalResidue_meromorphic` and `hga` drops out entirely.
2. **Direct Čech vanishing at genus 0**: Dolbeault comparison (`DolbeaultComparison*`) +
   an `H^{0,1} = 0` argument from the absence of holomorphic forms (Hodge-flavoured; the
   port deliberately avoided this PDE route).
3. **Uniformization-grade**: upgrade the degree-1-map machinery to a biholomorphism `X ≅ ℙ¹`
   without RR (open; `DegreeOneSphere.lean`'s remaining sorry is the bare-homeomorphism
   variant of exactly this wall).

Until one of these lands, `hga` stays a named hypothesis — exactly parallel to the spine's
R-lane-gated `{G, UnwindRegularity}` inputs. The keystone discharge equation is now:

```
exists_serreDualityData  =  hpos (lane R, g ≥ 1)  +  hga (this atom, g = 0)
```

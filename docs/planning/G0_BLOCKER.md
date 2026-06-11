# G0 blocker — the residual atom of the genus-0 keystone leg

*2026-06-10, branch `feat/keystone-g0-leg`. Companion to `G0_ROUTE.md` (route decision) and
`SerreDualityGenus0.lean` (the landed reduction).*

> **POST-TOWER UPDATE (2026-06-11, branch `feat/g0-atom`, `TailFrameGenus0.lean`).**
> The "research-grade" analysis below is PARTIALLY STALE: with both tail towers landed
> (`TailSurjectivity.lean`: `TailPairFrame.pairingSurjective` and
> `TailPairFrame.tailRiemannRoch` are **frame-only, genus-free**), the `hga` atom no longer
> needs a `SerreDualityData`-grade realization. The whole pipeline
> `TailPairFrame X → TailRiemannRoch X → hga` is proven, and the frame's `data`
> (`CanonicalForm17Data`, `ω₀ = df` MEROMORPHIC — `nonempty_canonicalForm17Data` is
> unconditional) and slot family (`formCoeff ω₀.toFun p`, exact order `K p` by `order_eq`)
> are free at every genus. **The ENTIRE residual is now one named lemma** (see
> "The exact minimal missing lemma" below); `TailFrameGenus0.lean` delivers `hga`, the
> uniform `h¹(𝒪) = g`, and the keystone `g = 0` leg conditional on it, kernel-verified
> standard-3. At `kirovGenus X > 0` the lemma is a THEOREM (`residueAtom_of_form`, via
> Gate A + the residue bridge), so the named hypothesis is the standard residue theorem,
> not a placeholder.

## The exact minimal missing lemma (2026-06-11)

```lean
-- vendor/kirov-dolbeault-port/KirovDolbeault/Dolbeault/TailFrameGenus0.lean
def CanonicalForm17Data.ResidueAtom (data : CanonicalForm17Data X) : Prop :=
  ∀ F : MeromorphicFunction X,
    ∑ p ∈ F.div.support ∪ data.K.support,
      planarCoeff (-1)
        (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * formCoeff data.ω₀.toFun p ζ)
        ((chartAt (H := ℂ) p) p) = 0
```

The failing goal at `kirovGenus X = 0` is to produce `∃ data : CanonicalForm17Data X,
data.ResidueAtom` — i.e. `∑ₚ Res_p(F·ω₀) = 0` for ONE nonzero MEROMORPHIC frame form
(e.g. `ω₀ = df`) and every global meromorphic `F`. Everything downstream of this is proven:

* `TailPairFrame.ofResidueAtom data hres : TailPairFrame X` (genus-free constructor);
* `h1Dim_zero_eq_zero_of_residueAtom` — **`hga` itself**;
* `exists_serreDualityData_of_genus_zero_of_residueAtom` — the keystone `g = 0` leg;
* `h1Dim_zero_chartDiskCover_eq_kirovGenus_of_genus_split` — `h¹(𝒪) = g` at the canonical
  cover with the atom needed in the `g = 0` case ONLY.

Why it cannot be factored through the proven Gate-A engine
(`SerreResidueTheorem.residueTheorem_unconditional`, statement `∑Res(α·g) = 0` for
`α : HolomorphicOneForms X`): a factorization `F·ω₀ = α·g` with `α` holomorphic and `g`
meromorphic requires `ω₀/g'` holomorphic for some global meromorphic `g'`, i.e.
`div ω₀ ≥ div g'` — impossible at genus 0 where `deg div ω₀ = 2g − 2 = −2 < 0` and no
nonzero holomorphic form exists. The engine's §5 slit tower (~15 files:
`ClusterTraceData`, `AdaptedFRamified`, `valueChartTrace`, `straightenedIntegrand`, …) is
parameterized by `coeffAt (α : HolomorphicOneForms X)` throughout, with `α`'s everywhere-
analyticity consumed in the branch-value comparison (`αBr`) and pole bookkeeping
(`hpoles` covers only `g`'s poles). Honest discharge routes, in rough order of cost:

1. **Engine generalization** — re-parameterize the §5 slit tower over a meromorphic frame
   read (`formCoeff ω₀`), enlarging `poles` to `supp(div g) ∪ supp K`. Mechanical but
   multi-week (every structure in the `SerreResidueRamified*` family).
2. **Plain-trace specialization for `ω₀ = df`** — `Tr(F·df) = (Tr F)·dw` on `ℙ¹` (the
   change-of-variables Jacobian cancels), so only the PLAIN value trace of `F` along `f`
   needs the slit machinery; then the sphere-side rational `∑Res = 0` closes. Smaller
   analytic surface than 1 but still a slit-tower re-instantiation.
3. **Tate-style algebraic residues** (Serre GACC Ch. II) — bypasses all contour analysis;
   a new self-contained tower.

Partial discharges available cheaply (down-payments, not yet needed by the conditional
chain): `∑Res(dh) = 0` (exact forms — local, `planarCoeff (-1) (deriv H) = 0` by monomial
stripping) and `∑Res(dg/g) = deg div g = 0` (logarithmic — via the proven axiom-clean
`deg_div`). These give the atom for `F ∈ ℂ(f)` rational in the frame function but cannot
reach general `F` without the trace.

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

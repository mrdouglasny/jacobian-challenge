# E6 blocker analysis — why the `:678` de Rham sorry does NOT fall to the transport

*2026-06-10. Companion to the E6 delivery
(`vendor/kirov-dolbeault-port/KirovDolbeault/DegreeOneGenusTransport.lean`).
This is a STATEMENT-level blocker, not a dependency-size blocker: the ported
transport landed in full, axiom-clean, on the first compile; what cannot land
is the literal discharge of the port sorry at `DegreeOneSphere.lean:678`
(now `:703`).*

## What E6 asked

Close the port sorry `(sorry : Jacobians.HasHolomorphicPrimitives X)` inside

```lean
theorem genus_zero_of_nonempty_homeo_sphere
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    kirovGenus X = 0
```

by porting our axiom-clean biholo-genus-transport
(`Jacobians/RiemannSurface/DegreeOneGenusZero.lean:388–451`) onto the port's
proven "single simple pole ⇒ `X ≃ₜ S²`" chain, with gates "sorry count 4 → 3"
and "`#print axioms` on the formerly-sorried decl = standard 3".

## The mismatch

The transport consumes **analytic** data: a holomorphic degree-1 map
`F : X → ℂℙ¹` whose inverse is holomorphic, so `pullbackForm` transports
`Ω(ℂℙ¹) ≃ₗ Ω(X)` and `kirovGenus X = kirovGenus ℂℙ¹ = 0`.

The sorried statement's hypothesis is a **bare topological homeomorphism**
`X ≃ₜ S²`. It carries no complex structure, hence no holomorphic map in either
direction, hence nothing to pull forms back along. Producing a holomorphic
degree-1 map from the hypothesis would require either

- **Riemann–Roch** (`exists_singleSimplePole_of_genus_zero`) — keystone-gated
  AND circular here (it needs `kirovGenus X = 0`, the goal); or
- **uniformization** ("every complex structure on the 2-sphere is standard") —
  research-grade, far beyond the de Rham wall it would replace.

So the classical content of the bare-homeo statement is irreducibly
"topological genus controls analytic genus", whose only port-feasible route is
the one rkirov isolated: `X ≃ₜ S²` ⇒ simply connected (proven, Van Kampen) ⇒
every holomorphic 1-form has a primitive (**the de Rham wall,
`HasHolomorphicPrimitives X`** — holomorphic Poincaré lemma / monodromy;
absent from Mathlib beyond balls in `ℂ`) ⇒ forms vanish by Liouville (proven).
The port's own docstrings (`GenusZeroOfSphere.lean`) state this; the gap
analysis' claim that the transport discharges this sorry "as a free
by-product" (`ABEL_WALL_GAP_ANALYSIS.md` §4 item 1(b), §5) is **overstated** —
its own caveat "coordinate with rkirov (it changes the advertised route of his
backward headline)" marks the issue. A correct reading: the transport deletes
the de-Rham-wall dependency *from the Abel chain*, not the de-Rham sorry
itself.

## What WAS delivered instead (the honest 90%)

`KirovDolbeault/DegreeOneGenusTransport.lean` (E6 commit series), all
`#print axioms`-verified `[propext, Classical.choice, Quot.sound]`:

| Decl | Content |
|---|---|
| `degreeOne_bijective` (DegreeOneSphere.lean refactor) | bijection extracted from `degreeOne_homeo` |
| `Jacobians.bijective_inverse_contMDiff` | bijective nonconstant `C^ω` ⇒ `C^ω` inverse (global injectivity ⇒ local injectivity ⇒ `deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood` ⇒ `exists_holo_localInverse` ⇒ congr) |
| `Jacobians.kirovGenus_eq_of_biholo` | `pullbackForm_id`/`_comp` ⇒ `LinearEquiv` ⇒ finrank equality |
| `Jacobians.genus_zero_of_singleSimplePole` | **single simple pole ⇒ `kirovGenus X = 0`**, keystone- and de-Rham-free |

Consequences:

- **Abel-wall A2+A3 closed.** The genus-obstruction half of
  `abelJacobi_twoPoint_ne_zero` (the snapshot's headline-critical sorry) no
  longer routes through `genus_zero_of_nonempty_homeo_sphere`: the future
  B-half proof composes with `genus_zero_of_singleSimplePole` directly (plus
  the A1 Finsupp bookkeeping `div f = (P) − (Q) ⇒ HasSingleSimplePole`, a
  separate "M"-rated item, not in E6 scope).
- **De Rham sorry reclassified, not discharged.** It now gates ONLY the
  backward half of the conformance headline `genus_eq_zero_iff_homeo`
  (`GenusSphereHeadline.lean`) — off the `ofCurve_inj` critical path. Port
  sorry count stays **4** (gate deviation, justified above); the PROVENANCE.md
  sorry table records the reclassification.

## Note on the cheaper port-side inverse-holomorphy proof

Our parent proof derives inverse holomorphy from "local mapping order 1
everywhere" via our weighted-fiber-conservation machinery
(`mapAnalyticOrderAt`, `weightedFiberConservation_of_contMDiff`), which has no
port analog and would have been a large porting cone. The port's degree
discharge already contains the two pieces that substitute for it:
`Jacobians.Discharge.ContMDiff.Degree.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood`
(local injectivity ⇒ chart-derivative nonzero; the ZZ99 planar bridge) and
`Jacobians.exists_holo_localInverse` (manifold IFT). This is the "port the
minimal cone" branch of the E6 instructions: the minimal cone turned out to be
empty — everything needed already existed port-side.

## Options for actually closing the `:703` sorry (decision: MRD + rkirov)

1. **Leave it** as the honest de Rham wall (status quo; recommended). It is
   now conformance-only; the challenge-critical cone is free of it.
2. **Restate the backward headline** to take the single-simple-pole data —
   breaks the advertised `genus_eq_zero_iff_homeo` conformance signature
   (the anti-hack constraint); needs rkirov's agreement upstream.
3. **Prove the de Rham wall** (manifold holomorphic Poincaré lemma): line
   integrals + homotopy invariance on `X` — a genuine new workstream
   (cf. HI-1 Route B, Buzzard Zulip disc-primitive validation).

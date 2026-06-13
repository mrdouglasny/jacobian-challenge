# Do Buzzard's 24 requirements categorically determine the Jacobian?

*Local commentary — not pushed. Drafted 2026-06-13. Companion to
`docs/VALIDATION.md`, which already asserts non-categoricity (lines 37–39);
this doc gives the argument in full and records the Gemini deep-think vet.*

## Question

Buzzard's challenge (`Jacobians/Challenge.lean`, spec v0.4) asks for ~24
declarations: the data (`genus`, `Jacobian X`, the seven instances making it a
complex Lie group, `ofCurve`, `degree`, `pushforward`, `pullback`) and the
theorems (`genus_eq_zero_iff_homeo`, `ofCurve_self`, `ofCurve_inj`, the three
holomorphicity lemmas, the four functoriality lemmas, and
`pushforward_pullback : f_* ∘ f^* = deg(f) · id`).

Two questions:

1. **Categoricity.** Do these 24 pin the standard Jacobian *up to isomorphism*,
   or are there non-standard objects satisfying all of them?
2. **Repair.** If not, does adding the Albanese universal property close the gap?

## What the 24 force

The instance bundle `[CompactSpace][ConnectedSpace][ChartedSpace (Fin g → ℂ)]
[IsManifold 𝓘(ℂ, Fin g → ℂ) ω][AddCommGroup][LieAddGroup …]` forces `Jacobian X`
to be a **compact connected complex Lie group of complex dimension
`g = genus X`** — i.e. a **complex torus `ℂ^g/Λ`** (a connected compact complex
Lie group is abelian and is a torus; algebraicity is *not* forced). The
dimension is nailed by the chart model `Fin (genus X) → ℂ`, so product-padding
`J × T` is excluded.

On top of that the spec supplies an **injective** (for `g > 0`),
**base-point-preserving**, **holomorphic** Abel–Jacobi map `ofCurve`, and a
**functorial** push/pull structure with the **degree identity**
`f_* ∘ f^* = deg(f) · id`.

This kills the cheap hacks: `J = 0` dies to `ofCurve_inj` + `genus_eq_zero_iff_homeo`;
wrong dimension dies to the chart model; non-injective collapse dies to
`ofCurve_inj`.

## Claim: the 24 are NOT categorical

The gap has two layers.

### (a) The *data* is not pinned, even with the object fixed

Nothing ties `ofCurve` to the functorial structure. Scanning the spec:
`ofCurve` occurs only in `ofCurve_self`, `ofCurve_inj`, `ofCurve_contMDiff`;
`pushforward`/`pullback` occur only in their own functoriality + degree lemmas.
There is **no naturality axiom** `pushforward f ∘ ofCurve_X = ofCurve_Y ∘ f`
relating them, and nothing fixes the AJ map's normalization beyond `x₀ ↦ 0`.

So there is a **globally coherent alternative filling**: keep the standard
`Jacobian`, `pushforward`, `pullback`, but replace `ofCurve` by `-ofCurve`
(equivalently, precompose with any element of `Aut(J(X), 0)`, a group that can be
large). All 24 still hold — negation is holomorphic, injective, fixes `0`, and
the push/pull lemmas never mention `ofCurve`. Hence the *solution as data* is
provably non-unique; the spec does not even pin the AJ map up to the object's
automorphisms.

### (b) The *object* is not pinned to the standard analytic type

The 24 describe `Jacobian X` only as "*some* `g`-dimensional complex torus
admitting an injective functorial Abel–Jacobi map satisfying the degree
identity." The classical fact that singles out the Jacobian **among all tori
receiving a map from `X`** is **universality** (the Albanese property) — and that
is exactly what the spec omits. Specifically:

- **No generation clause.** `ofCurve '' X` is not required to topologically
  generate `Jacobian X`.
- **No universal factorization.** No clause says maps `X → A` to other tori
  factor through `ofCurve`.

One cannot recover universality from the functoriality package, for a structural
reason: `pushforward` and `pullback` are themselves *chosen data*, and the
naturality / degree identities only test `Jacobian X` against *other Jacobians*
(objects in the image of the same functor), never against an arbitrary complex
torus or abelian variety. Naturality internal to the image of a functor does not
represent the functor. So the degree identity, while a strong non-degeneracy
condition, does not collapse the candidate tori.

Candidates the 24 do not exclude therefore include, in principle:

- an **isogenous torus** `J(X)/G` (`G` finite) with `ofCurve' = π ∘ ofCurve`,
  for a torsion `G` chosen off the difference surface `Δ = {aj(x) - aj(y)}` so
  that `ofCurve'` stays injective. **This requires `g ≥ 3`** (Gemini correction,
  §vet): for `g = 1`, `Δ = J(X)`; for `g = 2`, every degree-0 class is `[p−q]`
  so `Δ = J(X)` again — any nontrivial isogeny then destroys injectivity. For
  `g ≥ 3`, `dim Δ ≤ 2 < g`, so `Δ` is a proper closed subvariety, torsion points
  off it are dense, and such `G` exists. The obstruction to *globalizing* this
  into a functor is real (see §vet (1b)(ii)), but it shows the single-object
  constraints don't see the isogeny class;
- more generally, a torus of the right dimension with a **different complex
  structure** that still admits an injective AJ map.

The point is not that a fully coherent non-standard *functor* is exhibited here,
but that the 24 contain **no lever** forcing the complex-analytic isomorphism
type — categoricity is simply not among the things asserted, and the missing
ingredient is universality.

This matches `docs/VALIDATION.md`: "the 24 do **not** categorically pin the
Jacobian, so that residual doubt never fully closes. Efficiency comes from
*categoricity*, not length."

## Repair: Albanese universality closes (b), and (a) up to unique iso

The universal property makes `(Jacobian X, ofCurve x₀)` an **initial object** of
the category 𝒞_X of pointed holomorphic maps from `X` to complex tori (targets of
*any* dimension). By Yoneda, an initial object is **unique up to unique
isomorphism**. Hence any `(J, aj)` satisfying it is canonically and
base-point-preservingly isomorphic to the standard Jacobian. This:

- **closes (b):** no non-standard torus satisfies the universal property;
- **closes (a) up to the unique iso:** the factorizing isomorphism is unique and
  pointed, so the AJ map is pinned — the `-ofCurve` model now fails, since `-1`
  is not the *unique* factorizing hom unless it is the identity.

This is exactly what the repo encodes: `IsJacobian` (`UniversalProperty.lean:93`)
is the Albanese property quantified over complex tori of any dimension, and
`ofCurve_isJacobian` (`:457`) proves the standard construction satisfies it —
currently modulo four axioms (`AX_PeriodCycleBasis` → T-GEN,
`AX_curve_generates_jacobian`, `AX_period_functoriality`,
`AX_torus_self_albanese`). Making that axiom-free is the validation endgame.

## Two caveats (so the claim isn't oversold)

1. **The test category must be right.** "Complex torus" = compact connected
   complex Lie group is the correct analytic category: a curve's Albanese is
   automatically an abelian variety, and a compact connected complex Lie group is
   a torus. So the characterization is faithful. (`IsJacobian`'s statement was
   cross-model vetted 2026-06-02: Gemini + Codex.)

2. **Universality pins the Jacobian-as-pointed-torus, not the polarization.**
   It determines the Albanese (Jacobian as a complex torus + AJ map) up to unique
   iso — exactly Buzzard's object. But "the standard concept of Jacobian" in its
   richest sense is a **principally polarized** abelian variety (theta divisor
   `W_{g-1}`, Torelli recovering `X`); the polarization comes from the
   intersection form on `H₁` and is seen by neither the 24 nor the bare universal
   property *as part of its categorical signature*. So Albanese universality is
   necessary and sufficient for the *challenge's* notion and fully resolves
   categoricity as posed; pinning the ppav (and hence Torelli) is a strictly
   further addition. **Refinement (Gemini, §vet):** the polarization is not
   *given* by the UP but is *canonically derivable* from it — the Albanese
   property forces `aj_* : H₁(X,ℤ) → H₁(J,ℤ)` to be an isomorphism, and pushing
   the curve's canonical intersection pairing forward along it yields the unique
   principal polarization. So recovering the ppav in Lean is extra *work* but
   involves **no non-canonical choice**.

## Bottom line

The 24 are a sound non-degeneracy specification but not a definition-up-to-iso.
Adding the Albanese universal property is the right and minimal upgrade to
categoricity, and it is already built (`IsJacobian` / `ofCurve_isJacobian`); the
remaining work is discharging its four axioms, not stating anything new.

---

## Gemini vet

Vetted **2026-06-13** with **gemini-3.1-pro-preview** (deep-think's MCP endpoint
was down — legacy-API 400; 3-pro-preview 404'd; used 3.1-pro chat). One focused
query, all numbered claims. Verdicts:

| Claim | Verdict | Note |
|---|---|---|
| (0) instances ⟹ complex torus `ℂ^g/Λ`, dim pinned to `g` | **Sound** | compact ⟹ const global holos ⟹ abelian; `exp` is a covering; chart model locks `g` |
| (1a) data non-uniqueness (`-ofCurve`) | **Sound** | "perfect elementary counterexample"; `-aj` keeps holo/base/inj |
| (1b)(i) functoriality ⇏ universal property | **Sound** | functoriality internal to the system is a structural constraint, not a characterization |
| (1b)(ii) isogeny injectivity + globalization obstruction | **Sound-with-correction** | injectivity trick **needs `g ≥ 3`** (`Δ = J` for `g = 1, 2`); functorial choice of `G(X)` is the genuine global obstruction — confirmed |
| (2) Albanese UP ⟹ unique-iso, closes (1a)+(1b); test category correct | **Sound** | initial object unique up to unique iso; a curve's Albanese is exactly the universal torus |
| (3) UP gives torus-with-AJ, not the ppav/Torelli | **Sound-with-correction** | polarization not in the signature but **canonically derivable** by pushing `H₁`'s intersection form along the forced `aj_*` iso |

The two corrections (genus restriction on the isogeny example; polarization
derivable-not-given) are folded into the body above. Gemini's closing advice
matches the repo's direction: replacing the disconnected axioms with *(complex
torus) + (Albanese UP)* locks the object up to unique iso and makes
`f_*∘f^* = deg·id` a *consequence* rather than a separately-imposed axiom.

## Can we exhibit a non-Jacobian object passing the 24? (follow-up)

**Yes — there is a clean, fully compiled object-level counterexample.** It does
*not* require any of the subtle isogeny/complex-structure ideas; it exploits a
flat under-specification: **`genus` is pinned only at zero.** `genus_eq_zero_iff_homeo`
constrains the vanishing locus of `genus`; nothing equates `genus X` with the
topological genus for `genus ≥ 1`. The map `n ↦ 2n` preserves "= 0", so:

> `genus₂ X := 2·genus X`,  `Jacobian₂ X := Jacobian X × Jacobian X`,
> `ofCurve₂ := diagonal of ofCurve`,  `pushforward₂/pullback₂ := componentwise`,
> `degree₂ := degree`

satisfies **every one of Buzzard's 24** — but `Jacobian₂ X` is a `2g`-dimensional
torus, not isomorphic to the genuine `g`-dimensional Jacobian when `g > 0`.

This is **machine-checked**: `docs/categoricity/GenusDoublingCounterexample.lean`
(`lake env lean`, exit 0). It proves all seven instances (over the product model
`ModelProd (Fin g→ℂ)(Fin g→ℂ)`, which `finrank_model_eq_genus₂` certifies has
complex dimension `2g = genus₂ X`), `genus₂_eq_zero_iff_homeo`, `ofCurve₂_self`,
`ofCurve₂_inj`, `ofCurve₂_contMDiff`, the four functoriality lemmas,
`pushforward₂_pullback`, and the capstone `genus₂_ne_genus`. The one cosmetic gap
is that the chart model is the product space rather than the literal `Fin (2g)→ℂ`
— a linear change of coordinates (the two are `≅` as `2g`-dim ℂ-spaces, certified
by the finrank lemma), with no mathematical content.

So the literal 24 are **decisively non-categorical**, and the cheapest fix Buzzard
could make is to also pin `genus` (e.g. `genus X = topological genus`, or define it
as `finrank H⁰(Ω¹)`). Two footnotes:

- The earlier *data-level* observation (`-ofCurve`) is **not** a genuine
  counterexample: `-1` is an automorphism of the same torus, inside the inherent
  `GL`-ambiguity of the `H⁰(Ω¹)`/`H₁` basis. Same object. Dropped.

- **With `genus` pinned to the true genus, the 24 ARE categorical** —
  `T(X) ≅ J(X)` as complex tori for all `X`, no counterexample exists. This is a
  genuine rigidity theorem (Gemini deep-think, 2026-06-13; full argument in
  `commentary/deep-think-query-fixed-genus-categoricity.md`). The structure:
  (i) the degree identity makes `H₁(T(·),ℚ)` a representation of the semisimple
  category of curve motives, forcing `T(X)` isogenous to `J(X)` for *all* curves;
  Albanese factorization gives `T(X) ≅ J(X)/G_X`. (ii) Functoriality + the degree
  identity *alone* do NOT pin `G_X` — there are nontrivial functorial subgroups
  (seed a torsion point `v ∈ J(X₀)` and take `G_Y := Σ_{h∈Hom(J(X₀),J(Y))} h(v)`),
  refuting the "only `J[n]`" intuition. (iii) What kills them is **`ofCurve_inj`**:
  the same functorial object must admit an injective AJ map for *every* curve, and
  the difference surface `Y−Y` sweeps across moduli (Brill–Noether count) to hit
  any nonzero torsion seed, destroying injectivity unless `G_X = 0`. So the
  load-bearing axiom is injectivity, not functoriality — vindicating Buzzard's
  design intuition that `ofCurve_inj` does real work.

  Upshot for the challenge: a solver who fills the 24 honestly **with `genus` =
  true genus** has necessarily built (an object isomorphic to) the Jacobian. But
  the *proof* of that is non-elementary (motives + Brill–Noether); the Albanese
  UP (already built: `IsJacobian` / `ofCurve_isJacobian`) is the clean,
  formalizable certificate of the same fact, and also repairs the genus gap in
  one stroke. (Two steps of the rigidity proof — motivic semisimplicity, the
  exact Brill–Noether count — are noted as not independently line-checked.)

## Formalizability: don't formalize the rigidity proof — use the UP

Can Gemini's `24 + Condition 25 ⟹ T(X) ≅ J(X)` be formalized in Lean? **The proof
itself: no.** Its three load-bearing inputs are all absent from Mathlib and each is
a major project in its own right:

| Step of the rigidity proof | Mathlib prerequisite | Status |
|---|---|---|
| isogeny for *all* curves (not just simple) | semisimplicity of Chow motives of curves /ℚ | essentially nothing on Chow motives |
| functorial subgroups `G_X` exist | simple abelian varieties, Poincaré reducibility, isogeny-from-simplicity | almost no AV theory (repo has `ComplexTorus`, not AVs) |
| the kill (moduli sweep) | Brill–Noether dimension counts + "very general curve has `End J = ℤ`" (monodromy) | both absent — research-grade AG |

This is **strictly harder than Buzzard's challenge itself** (it presupposes the
Jacobian *plus* motives, Brill–Noether, and moduli/monodromy). Not a target.

**The conclusion it certifies is formalizable cheaply — via the Albanese UP, and
now mechanized.** The two are different routes to the same fact: Gemini's route is
`24 + Cond 25 ⟹ ≅ J` (hard); the UP route is `IsJacobian x₀ T aj ⟹ T ≅ J`
(one-line Yoneda). The categoricity theorem is proved in the repo itself —
`Jacobians/UniversalProperty.lean`, `isJacobian_unique` (builds via
`lake build Jacobians.UniversalProperty`): any two objects satisfying `IsJacobian`
are biholomorphically, group-isomorphically the same, via mutually inverse
holomorphic homs intertwining the AJ maps — and it is **axiom-free**
(`#print axioms Jacobians.isJacobian_unique` → `propext, Classical.choice,
Quot.sound` only). It uses **none of the 24**: the proof is pure initial-object
algebra over the three fields of `IsJacobian` (the holomorphy/basepoint facts it
needs are fields of the UP predicate itself). The corollary `isJacobian_iso_jacobian`
specializes one object to Buzzard's concrete `Jacobian X` via `ofCurve_isJacobian`
(this is where the 4 torus axioms enter). The UP route is *strictly better* than
adding Condition 25, because the UP also closes the genus-doubling gap on its own:
`J × J` with the diagonal fails the UP (both projections `φ(a,b)=a` and `φ(a,b)=b`
factor the diagonal AJ, so the factorizing hom is not unique). So the UP forces
the right dimension without a separate genus axiom.

So the answer to "can we formalize that 24 + Albanese determines the Jacobian?" is
sharper than expected: **Albanese alone determines it, axiom-free, and it's done**
— you need none of the 24, only the UP predicate. The 24 enter only to certify the
*concrete* construction is one such object (`ofCurve_isJacobian`).

What *is* mechanized, in `docs/categoricity/Condition25.lean` (compiles,
`lake env lean`, exit 0):

* `GenusEquality X` — Condition 25, `genus X = finrank ℂ (HolomorphicOneForm X)`;
* `repo_satisfies_condition25 : GenusEquality X := rfl` — the repo's filling
  satisfies it definitionally;
* `genusDoubling_violates_condition25` — the doubled model fails it for `g > 0`;
* `Condition25.rigidity` — Gemini's theorem **recorded as an `axiom`, not proved**,
  over a reified `Model` of the challenge data. (The 24-condition bundle
  `Satisfies24` is a `True` placeholder there — the file documents the *statement*
  and its provenance, it does not encode all 24 conjuncts.)

Bottom line: Gemini's proof is the right *mathematical* confirmation that the spec
is sound once `genus` is pinned; the right *formalization* is the Albanese UP,
which the repo has already chosen and largely built.

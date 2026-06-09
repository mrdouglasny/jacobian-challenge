# Challenge Layer 3 — standard differential-geometry / sheaf infrastructure

*Draft 2026-06-08. The missing rung in the reduction tower. Codex's Mathlib audit
([`FORSTER_ROUTE1_BUILD_PLAN.md`](FORSTER_ROUTE1_BUILD_PLAN.md)) showed the inputs
Forster §§13–21 consume are mostly absent from Mathlib (months-to-years to build).
Rather than build them now, axiomatize them as a **faithful, shallow, separately-
discharge-planned Layer 3**, and prove RR + Serre + the period cluster (the 9 deep
axioms) as **theorems over Layer 3**. The trust boundary descends from "9 classical
theorems" to "~5 standard, Mathlib-roadmap primitives."*

## The tower

```
Challenge 1 (Buzzard interface)        ⟸ axiom table
Challenge 2 (RR/Serre subchallenge)    ⟸ RR + Serre + period cluster   (9 axioms)
Challenge 3 (THIS)                      ⟸ Layer-3 infrastructure primitives (~5)
endgame                                 ⟸ Mathlib (build/upstream L3)
```

Net: the **9 deep axioms become theorems**; the kernel rests instead on ~5
*shallower, more-clearly-true, upstreamable* primitives. This is a real structural
reduction **iff** the two conditions below hold.

## Condition A — the primitives are PRIMITIVE + faithful (not the results in disguise)

Each is an opaque-but-faithful infrastructure axiom, with the full vetting protocol
(citation, satisfiability witness, Gemini review, `(NOT VERIFIED)` until vetted)
*before* anything rests on it. **A wrong statement here is a false kernel** — this
is the main risk and the real work. Candidate set (signatures are sketches to be
firmed + vetted, not final):

| Primitive | Asserts (faithful target) | Used by |
|---|---|---|
| **L3-Forms** | the de Rham complex on `X`: smooth ℂ-forms `Ω⁰,Ω¹,Ω²`, `d` (`d²=0`), `∧`, and `∫_X : Ω²(X) → ℂ` (integration of top forms; `X` compact oriented) | everything below |
| **L3-Stokes** | `∫_X dα = 0` for `α : Ω¹(X)`; residue form `∫_X d(f·σ) = 2πi · ∑_p res_p(...)` (the **cheap** surface-Stokes — punctured-disc boundary, NOT 4g-gon) | Serre §17, Abel §20, periods §21 |
| **L3-Dolbeault** | `∂̄`-Poincaré: local solvability `∂̄u = f` ⇒ (with Mathlib's sheaf LES) the Dolbeault iso `H^{0,1}(X) ≅ H¹(X,O)` | RR/Serre §16–17, harmonic §19 |
| **L3-Hodge** | the `⋆` operator on `Ω¹` (`⋆² = −1` on a surface) + **positivity** `i∫_X ω∧⋆̄ω > 0` for `0 ≠ ω` | Riemann bilinear §19, periods §21 |
| **L3-PD** | `H₁(X;ℤ)` free of rank `2g`, and the intersection pairing `H₁×H₁→ℤ` is **unimodular** (integral Poincaré duality / fundamental class) | cycle basis, intersection form, periods §21 |

The holomorphic structure sheaf `O`/`Ω¹` (Mathlib *TODO*) is either a thin L3 add-on
(opaque sheaf with the right sections) or built from L3-Forms; decide during the
RR-probe.

## Condition B — the reductions are weeks-scale Lean over the primitives

Codex's "months" was for *building* the infrastructure; the bet is that *given*
clean L3 axioms, the §16–21 assembly is tractable (Gemini: the math is elementary
homological algebra + form algebra). **Must be probed, not assumed.** Reduction map:

| Target (deep axiom) | Theorem over Layer 3 | Primitives used |
|---|---|---|
| `AX_RiemannRoch` | skyscraper SES `0→O(D)→O(D+P)→ℂ_P→0` + Mathlib LES (`Ext.covariantSequence`) + #116 finiteness | L3-Dolbeault, O |
| `AX_SerreDuality` | residue pairing `H¹(O(D)) × H⁰(Ω¹(−D)) → ℂ` nondegenerate | L3-Stokes, L3-Dolbeault |
| `AX_RiemannBilinear` | `∫ω∧ω=0` (type (2,0)=0) + `i∫ω∧⋆̄ω>0` | L3-Hodge, L3-Forms |
| `intersectionForm` (+alt, +perfect) | `∫_X α∧β`; alternating trivial; perfect = unimodular | L3-Forms, L3-PD |
| `AX_AnalyticCycleBasis` | `unimodular alternating ℤ-form ⇒ symplectic basis` (pure linear algebra) | L3-PD |
| `AX_PeriodLattice` | periods of the `g` forms over the `2g` cycles; full rank via Hodge nondeg | L3-Hodge, L3-PD, L3-Stokes |
| `AX_H1FreeRank2g` | part of L3-PD (free rank `2g`) | L3-PD |

## The decisive probes (de-risk Condition B before drafting all primitives)

1. **Symplectic basis (cleanest; pure linear algebra, NO infra axiom).** Prove
   `(M free ℤ-module, B alternating + unimodular) ⇒ ∃ symplectic basis`. Axiom-free,
   reusable, discharges the core of `AX_AnalyticCycleBasis` regardless of Layer-3's
   fate. **← starting here.** If it lands, one reduction is real.
2. **RR via LES (most informative; tests the cohomology pattern).** Given `O` + the
   skyscraper SES, extract `χ(D+P)=χ(D)+1` from `Ext.covariantSequence`. Confirms the
   §16–17 reductions are assembly-not-research over clean axioms.

If both land cleanly → draft + Gemini-vet the full L3 primitive set, then build the
reductions phase by phase. If the cohomology probe (2) bogs down even over clean
axioms → Layer 3's cohomology half is not weeks-scale; keep RR/Serre axiomatized and
harvest only the independent reductions (symplectic basis, bilinear).

## Honest framing (for README / AXIOM_AUDIT when L3 lands)

"RR, Serre, and the period cluster are **theorems**, reduced to a declared layer of
standard differential-geometry / sheaf-cohomology infrastructure (manifold forms,
Dolbeault, Hodge ⋆, surface-Stokes, integral Poincaré duality) — itself axiomatized
pending a Mathlib-grade build, not proved from Mathlib." Same honesty bar as Layers
1–2; the win is a *shallower, upstreamable* trust boundary + the reduction structure.

*Vetting: this layering proposed by the owner 2026-06-08 after the Gemini (math) +
Codex (Mathlib) Route-1 vettings. Each L3 primitive re-vetted before reliance.*

---

## SCOPE VERDICT (2026-06-08, both probes complete): **GREEN — viable, ~2–3 months, gated on sheaf-model faithfulness**

**Probe 1 (linear-algebra reductions): GREEN.** `exists_symplectic_basis` (field
Darboux) landed sorry-free, axiom-free (`784c1c7`, branch `layer3-symplectic-basis`).
The ℤ lift (for `AX_AnalyticCycleBasis` on `H₁(X;ℤ)`) needs **one** Mathlib-grade
integral-lattice-splitting lemma (`unimodular alternating ℤ-form splits off a
hyperbolic plane`: `M = span{v,w} ⊕ ᗮ`, complement finite-free + restricted-
unimodular) — weeks, or a clean L3-PD-adjacent axiom.

**Probe 2 (cohomology reductions): GREEN engine, sheaf-model is the cost.** The RR
Euler-characteristic engine `eulerChar_additive_of_exact_six` (+ skyscraper
corollary) landed sorry-free, axiom-free (`9e3fa8c`, branch `layer3-rr-probe`) via
`Function.Exact` + rank-nullity. **But** the project has only *global* meromorphic
infrastructure (`riemannRochSpace D` is a global submodule); a real sheaf `O(D)` —
local sections, gluing, the skyscraper SES, the `Sheaf.H 0 (O(D)) ≅ L(D)` bridge —
is unbuilt. Mathlib has the substrate (`Sheaf.H`, `Ext.covariantSequence`,
`skyscraperSheaf`) but **not** holomorphic/meromorphic sheaves (TODO). Estimate
(Probe 2): **3–6 weeks just to *state* a credible axiomatized sheaf model + bridges**
(the project's own `SheafCohomologySpec` flags it as not-yet-faithfully-stateable),
then a few hundred LOC to assemble RR over it.

**Net:** Layer 3 is real. The reductions are tractable (proven). The dominant cost
+ the faithfulness risk both live in **stating the `O(D)`-sheaf primitive** — a
wrong sheaf axiom is a false kernel, and it's the hardest thing to state right.

## Implementation phasing

- **Phase A — analytic primitives + their *non-sheaf* reductions (lower risk; start here).**
  L3-PD ⇒ symplectic basis (field done; build/axiomatize the ℤ-splitting) +
  intersection form; L3-Hodge ⇒ Riemann bilinear (`∫ω∧ω=0` by type, `i∫ω∧⋆ω̄>0`).
  Discharges `AX_AnalyticCycleBasis`, `intersectionForm(+laws)`, `AX_RiemannBilinear`,
  `AX_H1FreeRank2g` over L3-PD/L3-Hodge — **no sheaf model needed.**
- **Phase B — the sheaf-model core (the risky 3–6-wk design).** Faithfully axiomatize
  `O(D)` sheaf + skyscraper SES + `H⁰≅L(D)` bridge; assemble RR (§16) via the
  Euler-char engine + Dolbeault; Serre (§17) via the residue pairing. **Design + Gemini-vet
  the sheaf axioms BEFORE building** (faithfulness-critical).
- **Phase C — period lattice (§19/§21).** Harmonic forms (L3-Dolbeault+L3-Hodge) ⇒
  `AX_PeriodLattice`; Abel ⊇ already underway.

Each L3 primitive gets the full axiom-vetting protocol (citation, satisfiability
witness, Gemini review, `(NOT VERIFIED)` until cleared) before any theorem rests on it.

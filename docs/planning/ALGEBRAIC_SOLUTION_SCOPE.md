# ALGEBRAIC_SOLUTION_SCOPE — the minimal route-(b) function-field/adelic plan

*Scoping document for the "minimal algebraic solution" to Buzzard's Jacobian
Challenge sketched in `docs/FOUNDATIONS.md` §4/§4½ (route b: function field /
Weil adeles, **not** projective-scheme/Chow). Read-only analysis; no Lean code
and no axioms were touched in producing it. Every claim is cited `file:line`
against the tree at branch `feat/algebraic-scope` (= `origin/main` at the time
of writing). Written 2026-06-12.*

---

## 0. Executive orientation

FOUNDATIONS §4 proposes a four-layer minimal design. This document turns that
sketch into a concrete, critically-assessed implementation plan, with a real
Mathlib inventory and named-lemma ladders, and asks the only question that
matters for a go/no-go: **does the adelic route actually buy what §4 claims it
buys?**

The headline finding, established below and confirmed by an external review
(Gemini 3 Pro, §6), is uncomfortable and worth stating up front:

> **The adelic route does not avoid the analytic Riemann–Roch inequality — it
> *consumes* it.** The Weil adelic development of finiteness (`adeleH1` is
> finite-dimensional) and of Serre-duality *nondegeneracy* logically depends on
> one of two heavy inputs that §4½ underplays: **either** (i) the
> transcendence-degree-1 crossing `K(X)` is a finite extension of `ℂ(f)`
> *together with the algebraic trace map on differentials*, **or** (ii) an
> already-proven Riemann inequality `l(D) ≥ deg D + 1 − g` — which in this tree
> exists only via the Čech/Dolbeault tower the route was meant to delete.

So the §4½ claim "Mathlib already carries the backbone for everything downstream
of the crossing" is **half-true**: Mathlib carries the *adele ring and valuation
algebra*, but it carries **no Riemann–Roch, no genus, no algebraic differentials
/ trace map, and no residue pairing** (§4 inventory), and those are exactly the
pieces the adelic RR/Serre proof needs. The crossing is not "light"; it is the
load-bearing wall, and it sits in front of *another* wall (the trace map or the
imported analytic inequality).

This does **not** make route (b) worthless — Layers 0 and 3 are essentially done
and reusable, and the *statements* (`adeleH1`, repartitions, `L(D)`) are already
formalized and well-defined in-tree, which is real progress. But the
"well under 20,000 lines, drops the 35k Čech tower" budget in §4 is **not
achievable while keeping the route honest**: the Čech tower (or an equivalent
analytic finiteness result) cannot be dropped — at most it can be *quarantined*
behind the single Riemann-inequality interface that the adelic layer imports.

**Bottom line (full detail in §7):** Go/no-go = **conditional go for the
*statements and packaging* (Layers 0,1-statement,2-definitions,3 are reusable and
mostly done), NO-GO for the claim that route (b) is cheaper than the analytic
tree.** The minimal *honest* algebraic solution is ~**8–13k new lines** on top of
the reused seed, and its critical path runs straight through either the
trdeg-1 + algebraic-trace crossing (research-grade in Lean today) or a retained
analytic Riemann inequality (i.e. you keep a slice of the tower you wanted to
delete).

---

## 1. Layer 0 — the analytic seed (what the tree already has)

**Status: DONE and reusable. Reuse ≈ 100%.**

The seed is the Cauchy–Pompeiu atom and the two facts it grows into (residue
theorem; ∂̄-solvability ⇒ existence of meromorphic functions). All three are
present as real theorems in the vendored Dolbeault port, already compiled in our
build.

| Seed piece | Location | Status |
|---|---|---|
| Cauchy–Pompeiu atom (`integral_dbar_smearedSimplePole`, `resNormalization_integral_eq_one`, `exists_signTest_witness`) | `vendor/kirov-dolbeault-port/KirovDolbeault/Dolbeault/FineResidue/SignTest.lean:104,146,158` | theorem |
| Residue theorem `∑ Res = 0` (`residueTheorem_unconditional`) | `vendor/.../Dolbeault/SerreResidueRamifiedRealSlitGeometry.lean:1017` | theorem |
| ∂̄-solvability / Abel engine (`exists_meromorphic_of_zeroPeriodChain'`) | `vendor/.../Dolbeault/AbelSubsetEngineArc.lean:2133` | theorem |
| Existence of a nonconstant meromorphic function (`exists_nonconstant_meromorphic`, `exists_nonconstant_meromorphicFunction`) | `vendor/.../Dolbeault/SerreOmega0.lean:129,181` | theorem |

**Critical caveat for the budget.** §4 calls the seed "~1k new lines over
Mathlib". That is true *only for the atom itself* (`SignTest.lean` is 173 lines;
`DbarDisk` adds the rest of the ~970). But `exists_nonconstant_meromorphic` is
**not** a thin corollary of the atom: its proof (SerreOmega0.lean:129) runs
through `two_le_lDim_largeEffective` — a **Riemann–Roch *inequality*** — which is
itself a product of the larger ∂̄/Leray apparatus in the port. The seed-as-stated
("residue theorem + ∂̄-solvability") already silently contains an RR-inequality
engine. This matters enormously for Layers 1–2 (see §6).

**Reusable here:** everything. The seed needs no new work; it is the one part of
§4's budget that is honest as written.

---

## 2. Layer 1 — the function-field crossing

**Status: PARTIALLY built (the multiplicative group K(X)* and the branched
cover exist); the genuine analytic content — trdeg-1 / finite extension — is
ABSENT and is the crux. Reuse ≈ 40% of code, ≈ 0% of the hard content.**

### 2a. What is in-tree (reusable)

- **`MeromorphicFunctionField X`** — `K(X)*` as a `CommGroup` (nonzero global
  meromorphic functions modulo punctured-germ equality), with the full
  group-law proofs and the divisor homomorphism
  `divHom : K(X)* →* Multiplicative (Divisor X)`
  (`Jacobians/RiemannSurface/MeromorphicFunctionField.lean:364,390,453`).
  `orderSupport_finite` (the finite-pole theorem, MFF.lean:429) and
  `divisor_mul` (MFF.lean:445) are proven. **This is the local valuation theory
  the route needs, packaged as a divisor map — reusable as-is.**
- **The branched cover `X → ℙ¹`** — `toP1 : K(X) → (X → ProjectiveLine)`,
  holomorphic, with fiber-finiteness and weighted-fiber-sum data
  (`Jacobians/RiemannSurface/MeromorphicToP1.lean:630,684,692,704,712`) and a
  `Nonconstant` predicate (MeromorphicToP1.lean:727,730). **This is exactly the
  "one nonconstant f makes X → ℙ¹ a branched cover" object §4 step 4 calls for —
  and it already exists.**

### 2b. What is ABSENT (the crux)

The §4 step-4 claim — "assemble `K(X)` as an algebraic function field of one
variable … `K(X)` has transcendence degree 1 … this function-field crossing is
modest" — is **not realized in the tree at all**, and "modest" is wrong:

1. **`K(X)` is only a multiplicative `CommGroup`.** There is **no additive
   structure, no `Field` instance, no ℂ-algebra structure** on
   `MeromorphicFunctionField X` (grep confirms only `One/Mul/Inv/CommGroup`
   instances, MFF.lean:371-390). The Weil adelic development needs `K(X)` as a
   **field** (you add repartitions, you form `ℂ(f) ⊆ K(X)`). Building the
   additive field structure is itself non-trivial: addition of germ-classes is
   fine, but the *zero* element and the field axioms over the punctured-germ
   quotient need their own ~few-hundred-line development. (Note: `MeroField X` in
   `Cohomology/RiemannRochSpace.lean:155` *is* an additive ℂ-vector space of
   germ-classes — but it is **not a field** either, and it is a *different*
   quotient from `MeromorphicFunctionField X`; reconciling the two is unbudgeted
   work.)
2. **trdeg-1 / finite extension `[K(X):ℂ(f)] < ∞` is absent.** No `IsTranscendent`,
   no `Algebra.transcendenceDegree`, no `FiniteDimensional ℂ(f) K(X)` anywhere
   (grep: zero hits outside import lines).

### 2c. Is trdeg-1 actually needed? (the decisive question)

**Yes.** Confirmed by external review (§6, verdict A). The Weil adelic machine is
algebraic: the only reason the adele quotient `A_K/(A_K(D)+K)` is *finite*-
dimensional is the comparison to `ℙ¹` (= `ℂ(f)`), where dimensions are trivial,
pulled up the finite extension. Without trdeg-1 there is no *algebraic* reason
for finiteness — the quotient could be infinite-dimensional for all the adele
algebra knows. So Layer 1's "crux" step is genuinely on the critical path of
Layer 2.

### 2d. Difficulty of the trdeg-1 proof in Lean

The textbook proof (one nonconstant `f` ⇒ `X → ℙ¹` is a degree-`n` branched
cover ⇒ `[K(X):ℂ(f)] ≤ n`) is mathematically clean but **HARD to formalize
today**, for two reasons:

- It needs a genuine **degree theory** for the cover (the weighted-fiber-sum
  lemmas in MeromorphicToP1 are a start, but "all fibers have the same weighted
  cardinality `n`" — the *valence* theorem — is not proven there; that is the
  classical `deg(f⁻¹(0)) = deg(f⁻¹(∞)) = n` plus its constancy, only the `0`/`∞`
  fibers appear in-tree).
- The standard `[K(X):ℂ(f)] ≤ n` argument forms elementary symmetric functions
  of `g` over the fibers of `f` and proves they descend to *rational* functions
  on `ℙ¹`, which needs the **Riemann removable-singularity / extension theorem
  across the branch locus in a usable geometric form — a Mathlib gap** (§6, A).

### 2e. Named-lemma ladder (Layer 1)

| rung | statement | difficulty | LOC |
|---|---|---|---|
| L1.1 | Additive ℂ-algebra / `Field` structure on `K(X)` (reconcile with `MeroField`) | M | ~400 |
| L1.2 | `ℂ(f) ↪ K(X)` for nonconstant `f` (the `ℂ`-subalgebra generated by `f`, recognised as `RatFunc ℂ`) | M | ~250 |
| L1.3 | Valence: every fiber of `toP1 f` has weighted cardinality `n = deg f` (constancy of degree) | **H** | ~600 |
| L1.4 | Symmetric-function descent + removable singularity ⇒ `[K(X):ℂ(f)] ≤ n`, hence `FiniteDimensional ℂ⟮f⟯ K(X)` and `trdeg = 1` | **H / research-grade** | ~700 |
| L1.5 | Present the places of `K(X)` as a `HeightOneSpectrum` of the ring of integers `ℂ[f]`-integral-closure, matching points of `X` to valuations | M–H | ~500 |

**Layer 1 total: ~2.5k new lines, with L1.3–L1.4 the genuine wall.** Reuse from
the in-tree group + cover ≈ 40% of the *scaffolding*, but ≈ 0% of the hard
trdeg-1 content.

---

## 3. Layer 2 — adelic Riemann–Roch / Serre

**Status: the DEFINITIONS are fully built and proven well-defined; the three
theorems are open sorries and depend on Layer 1's missing crux. Reuse ≈ 60% of
definitional code, ≈ 0% of the theorem content.**

### 3a. What is in-tree (reusable — and more than §4 claims)

§4 says "the repo's `RiemannRochAnchor.lean` is exactly this, three sorries from
done". The reality is **better on definitions, worse on proofs**:

- **The whole repartition/adele layer is built and sorry-free:**
  - `IsRepartition`, `repartitions X` (the ℂ-submodule), `repartitionsBounded D`
    (= `A_K(D)`), `diagonalRepartition` (= `K_X ↪ A_K`), and the **finite-pole
    theorem** `diagonal_isRepartition` (Cohomology/Repartitions.lean:42,88,103,
    138,209 — all theorems, 0 sorries).
  - `adeleH1 D = repartitions ⧸ (A_K(D) ⊔ range K_X)`, with its `AddCommGroup`
    and `Module ℂ` instances (Cohomology/H1.lean:53,56,60).
  - `riemannRochSpace D = L(D)` as a proven ℂ-submodule, with `Effective`,
    `orderAtField`, the whole order calculus (Cohomology/RiemannRochSpace.lean:
    294, +supporting lemmas; 0 sorries).
- **`Divisor`, `deg`, `genus`** all exist (genus = `finrank ℂ HolomorphicOneForm`,
  `Jacobians/Challenge.lean:61`).

So the *Weil model itself is formalized and well-typed*. This is genuine, banked
progress and the strongest argument that route (b) is "viable on the same seed".

### 3b. The three open theorems (the sorries) and what they need

`Jacobians/RiemannSurface/Cohomology/RiemannRochAnchor.lean` (59 lines, 3 sorries):

| goal | statement (RiemannRochAnchor.lean) | classical input it needs |
|---|---|---|
| (1) `riemannRoch_anchor` | `finrank L(D) − finrank adeleH1(D) = deg D + 1 − g` | trdeg-1 + dimension count over `ℂ(f)`, OR an imported Riemann inequality (§6 B1) |
| (2) `adeleH1_finiteDim` | `FiniteDimensional ℂ (adeleH1 D)` | **the Riemann inequality** `l(D) ≥ deg D + 1 − g`; provable adelically *only* via the trace from `ℂ(f)` (§6 B1) |
| (3) `serre_anchor` | `∃ K, adeleH1 D ≅ Dual (L(K−D))` | **Serre nondegeneracy** = the "other half" of RR; the *surjectivity* obstruction needs the algebraic trace map on differentials **or** Mittag-Leffler ≡ `H¹(O)` (§6 B2) |

### 3c. The decisive Layer-2 findings (external-review-confirmed, §6)

- **B1 (finiteness):** `adeleH1(D)` finite-dim is algebraically *equivalent* to a
  Riemann inequality. That inequality is **not** provable inside the adeles from
  "residue theorem + pole-finiteness" alone. It must come from **either** the
  trdeg-1 finite extension (compute on `ℂ(f)`, lift by trace) **or** an imported
  analytic inequality. The tree's *only* such analytic inequality
  (`two_le_lDim_largeEffective`, used by `exists_nonconstant_meromorphic`) lives
  **inside the Čech/Dolbeault apparatus** — the very tower §4 wants to delete.
- **B2 (Serre nondegeneracy):** the residue pairing's *injective* half is the
  residue theorem (have it); the *surjective/nondegenerate* half is the deep
  half of RR and is **not** a formal consequence of the residue theorem +
  finiteness. Adelically it needs the algebraic trace map
  `Tr_{K(X)/ℂ(f)}` on differentials (**a Mathlib gap** — no algebraic Kähler
  differentials / trace API for function-field extensions, §6 B2); analytically
  it is Mittag-Leffler ≡ `H¹(X,O) = 0`-type content. **Goals (1) and (3) are
  essentially one theorem** (RR ⟺ Serre dimension count), so they do not add
  independently, but neither is "free over the residue theorem".

### 3d. Named-lemma ladder (Layer 2), under the two roads

**Road b-trace (pure adelic, no analytic import):**

| rung | statement | difficulty | LOC |
|---|---|---|---|
| L2.1 | `A_K(D)` is `ℂ(f)`-comparable: pull the quotient back along `ℂ(f) ↪ K(X)` | M | ~300 |
| L2.2 | RR for `ℙ¹` / `ℂ(f)` explicitly (base case; this part *is* elementary) | M | ~400 |
| L2.3 | algebraic trace map `Tr_{K(X)/ℂ(f)}` on `K(X)` and on differentials | **research-grade** (Mathlib-absent) | ~1500+ |
| L2.4 | lift RR + finiteness from `ℂ(f)` to `K(X)` via trace ⇒ goals (1),(2) | H | ~700 |
| L2.5 | Serre nondegeneracy via trace-of-differentials ⇒ goal (3) | **research-grade** | ~800 |

**Road b-import (adelic packaging over a retained analytic inequality):**

| rung | statement | difficulty | LOC |
|---|---|---|---|
| L2.1' | expose the in-tree analytic Riemann inequality as a clean interface lemma `l(D) ≥ deg D + 1 − g` (from the port / `H1coh`) | M | ~200 |
| L2.2' | finiteness of `adeleH1(D)` from the index bound ⇒ goal (2) | M | ~400 |
| L2.3' | RR dimension count adelically over the imported inequality ⇒ goal (1) | M–H | ~600 |
| L2.4' | Serre nondegeneracy by comparing `adeleH1` to the analytic `H1coh` (which already has Serre duality, §5) ⇒ goal (3) | M–H | ~600 |

**Layer 2 total:** road b-trace ≈ **4.5–5.5k lines incl. a research-grade trace
API** (and L2.3/L2.5 are the genuine hard spots); road b-import ≈ **1.8k lines but
keeps a slice of the analytic tower alive behind the interface** — i.e. it does
*not* deliver §4's "drop the 35k Čech tower" promise; it relocates the
dependency.

---

## 4. Mathlib inventory (the load-bearing assessment)

Grepped against `.lake/packages/mathlib/Mathlib` at the pinned toolchain.

### 4a. What Mathlib HAS (the adele/valuation backbone — usable, field-agnostic)

- **`IsDedekindDomain.HeightOneSpectrum`** (the places) —
  `RingTheory/DedekindDomain/Ideal/Lemmas.lean:495`, with the full adic-valuation
  API: `intValuation`, `valuation : Valuation K ℤᵐ⁰`,
  `intValuation_exists_uniformizer`, `intValuation_lt_one_iff_dvd`, etc.
  (`RingTheory/DedekindDomain/AdicValuation.lean:169,320,275,222`). This **is**
  "places = points, valuations = order of vanishing", and it is exactly what
  L1.5 must target.
- **`FiniteAdeleRing R K`** with `CommRing`, `TopologicalSpace`, `Algebra K`,
  `DFunLike` (component access), unit embedding `Kˣ → 𝔸ˣ`
  (`RingTheory/DedekindDomain/FiniteAdeleRing.lean:93,96,99,102,124,177`). The
  restricted-product adele ring is **there**.
- **`FunctionField F K` is FIELD-AGNOSTIC** — `abbrev FunctionField [Field F]
  [Field K] [Algebra F⟮X⟯ K] : Prop := FiniteDimensional F⟮X⟯ K`
  (`NumberTheory/FunctionField.lean:59`). **This applies to `F = ℂ`** — it is
  *not* `𝔽_q`-specific in its core definition (the `𝔽_q`-flavoured parts are the
  class-number / infinite-place completions, which route (b) does not need). So
  the §4½ hope "Mathlib's FunctionField is usable" is **correct at the definition
  level** — but note it presupposes you have *already* exhibited `K(X)` as a
  finite extension of `ℂ(X)` = `ℂ(f)`, i.e. it presupposes the L1.4 crux.
- **`differentIdeal`** (the ramification different) —
  `RingTheory/DedekindDomain/Different.lean:476`, with `differentIdeal_ne_bot`
  and the tower formula. Relevant to a canonical-divisor / Serre construction,
  but stated for ring extensions `A → B`, **not** curve-level; wiring it to the
  Serre canonical class is unbudgeted and non-trivial.

### 4b. What Mathlib LACKS (every gap is on the route's critical path)

- **NO Riemann–Roch.** `grep -rln 'RiemannRoch' Mathlib` = **zero files**.
- **NO genus** of a curve / function field.
- **NO residue pairing, NO Serre duality** of any kind.
- **NO algebraic Kähler-differentials trace map** on function-field extensions
  (the L2.3/L2.5 / §6-B2 gap) — `differentIdeal` exists but not the
  `Tr_{K/k(t)}` on `Ω`.
- **NO Riemann removable-singularity theorem** in a geometric branch-locus form
  (the L1.4 gap, §6 A).
- **`AlgebraicGeometry/FunctionField`** is the *scheme generic-point stalk*
  (`Scheme.functionField := presheaf.stalk (genericPoint X)`,
  `AlgebraicGeometry/FunctionField.lean`) — this is **route-(a) territory** and
  is **not** usable for route (b): it presupposes `X` is already a scheme, the
  exact thing route (b) avoids.
- **`NumberTheory/ClassNumber/FunctionField`** — `𝔽_q`-specific (finite residue
  fields, class numbers); **not applicable** to `ℂ(X)`.

**Inventory verdict:** Mathlib supplies the *plumbing* (adele ring, valuations,
the finite-extension definition) but **none of the theorems** — RR, genus,
differentials-trace, residue pairing, Serre. Every one of those gaps lands on the
critical path of Layers 1–2. The backbone is real; the route still has to build
all the mathematics.

---

## 5. Layer 3 — the Jacobian and Abel, lattice-direct

**Status: essentially DONE, sorry-free, axiom-free. Reuse ≈ 95%.**

This is the layer §4 calls "the K-FULL shape", and it is the one place the
counterfactual is already realized in the tree.

- **Discreteness (the K-LITE argument):**
  `discreteTopology_loopPeriodLattice` and the instance
  `instDiscreteTopology_loopPeriodLattice`
  (`Jacobians/RiemannSurface/PeriodDiscretenessKirovRoute.lean:1292,1316`) are
  proven **sorry-free and `AX_PeriodCycleBasis`-free** (the two "sorry" string
  hits in that file are the words "sorry-free" inside docstrings, lines 901/914 —
  there are no real sorries).
- **Rank `2g` from `ZLattice`:** `isZLattice_loopPeriodLattice` (:1325),
  `finrank_loopPeriodLattice_unconditional : finrank ℤ (loopPeriodLattice) =
  2 * genus X` (:1331). Pure linear algebra over Mathlib's `ZLattice`.
- **The Jacobi base-point / IFT / residue-read machinery** the discreteness proof
  needs (the Forster 21.3/21.4 ladder) is all in that file:
  `exists_jacobiBasePoints_det_ne_zero` (:253), the strict-Fréchet `jacobiMap`
  (:413), built on the seed's residue theorem.
- **Abel's theorem:** `Jacobians/Axioms/AbelTheorem.lean` and
  `Jacobians/RiemannSurface/AbelSupsetPlumbing.lean` are **0 sorries**, resting on
  the Abel engine (Layer 0) and the lattice.

**Reusable here:** essentially all of it, with no dependence on Layers 1–2. This
confirms FOUNDATIONS §3/§5: the lattice-direct Jacobian is real and the
cycle-basis axiom is gone on this path. **Layer 3 is not a cost in the algebraic
plan — it is a completed asset.**

The one residual FOUNDATIONS itself names (T-GEN, "analytic loops generate H₁",
elementary topology) is *outside* the adelic RR/Serre question this document
scopes, and is tracked elsewhere (KIROV_214_STUDY §3, the T-lane). It does not
move the algebraic-route go/no-go.

---

## 6. External review of the two hard spots (Gemini 3 Pro, 2026-06-12)

Deep-think was unavailable (API migration); the review below is Gemini 3 Pro
chat, asked one focused multi-part query on the two hard spots. Its verdicts
match the in-code reading and are recorded for the axiom/strategy ledger.

- **A (trdeg-1 crossing): HARD; logically REQUIRED.** "The Weil adelic proof
  logically strictly depends on `K(X)` being a finite extension of `ℂ(f)`. Pure
  algebra cannot 'see' that your ring of adeles comes from a 1-dimensional
  compact space unless you compare it to `ℙ¹`." The degree/symmetric-function
  proof needs the **Riemann removable-singularity theorem across the branch
  locus**, a Mathlib gap.
- **B1 (finiteness): MODERATE if importing the analytic inequality;
  RESEARCH-GRADE if trying to avoid BOTH trdeg-1 and the analytic inequality.**
  "You cannot prove [the Riemann inequality] natively inside the adeles using
  only the residue theorem and pole counting." Either lift from `ℂ(f)` via the
  trace, or import a previously-formalized (Čech/Dolbeault) finiteness result.
- **B2 (Serre nondegeneracy): HARD.** "Serre nondegeneracy is *not* a formal
  consequence of the residue theorem and B1. It is the deep 'other half' of
  Riemann–Roch." The injective half is the residue theorem; the surjective half
  needs the algebraic **trace map on differentials** (Mathlib-absent: "Mathlib …
  completely lacks the API for algebraic Kähler differentials and the algebraic
  trace map on differentials for finite extensions of function fields") or,
  analytically, Mittag-Leffler ≡ `H¹(X,O)`.
- **Reviewer's own recommendation:** "If your project has already formalized the
  analytic/Čech setup elsewhere in the tree … abandon the Weil route for Serre
  Duality. Use the analytic (Čech/Dolbeault) route. If you are committed to the
  Weil route, you *must* formalize the finite extension theorem and build the
  algebraic trace map. There is no shortcut that uses adeles but skips the
  algebra."

This is a single-model chat review (not the usual deep-think + Codex pair, due
to the deep-think outage); a high-leverage commitment to road b-trace should get
a second opinion (Codex) on the trace-map Mathlib gap before anyone starts L2.3.

---

## 7. Conclusion — LOC, critical path, go/no-go

### 7a. Reuse summary (per layer)

| Layer | reuse of existing code | reuse of the *hard content* | net new work |
|---|---|---|---|
| 0 — seed | ~100% (port) | ~100% | none |
| 1 — function field | ~40% (group + cover scaffolding) | ~0% (trdeg-1 absent) | ~2.5k |
| 2 — adelic RR/Serre | ~60% (definitions done) | ~0% (3 theorems open, depend on L1) | 1.8k (import) / 4.5–5.5k (trace) |
| 3 — lattice Jacobian + Abel | ~95% (sorry-free, axiom-free) | ~95% | ~0 |

### 7b. Total new-line estimate (honest, both roads)

- **Road b-import** (adelic packaging over a retained analytic Riemann
  inequality): **≈ 5–7k new lines** (L1.1–L1.2,L1.5 partial + L2.1'–L2.4').
  But it **keeps a slice of the Čech/Dolbeault tower alive** behind the
  inequality interface — it does **not** fulfil §4's "drop the 35k tower" claim;
  it quarantines the dependency to ~one interface lemma. Lower-risk, lower-purity.
- **Road b-trace** (pure adelic, trdeg-1 + algebraic trace map): **≈ 9–13k new
  lines**, of which L1.3–L1.4 and L2.3/L2.5 are **HARD / research-grade in Lean
  today** because of the removable-singularity gap and the absent algebraic
  differentials/trace API. Higher-purity, higher-risk; plausibly a multi-month
  effort dominated by building Mathlib-absent algebra.

Either way the §4 budget "well under 20,000 lines" is *numerically* plausible but
its companion claim — "most of the saving from replacing the analytic RR tower
with algebra" — is **not** borne out: road b-import keeps the tower behind an
interface, and road b-trace replaces the tower with an *equally large* new
algebraic edifice (trace map + removable singularities) that Mathlib does not
have.

### 7c. Critical path

```
   Layer 0 (done)
        │
        ▼
   L1.3 valence / degree-constancy ──┐
   L1.4 trdeg-1 / [K:ℂ(f)]<∞ ────────┤  ← THE WALL (removable-singularity gap)
        │                            │
        ▼                            │
   L2.3 algebraic trace map ─────────┘  ← THE SECOND WALL (Kähler-diff/trace gap)
        │
        ▼
   goals (1)(2)(3) on adeleH1   ←  (1)≡(3) dimension count; (2) follows from finiteness
```

For **road b-import**, the critical path instead runs `L2.1' (expose the analytic
inequality) → L2.2'–L2.4'`, and the "wall" is conceptual honesty rather than
math: you are no longer giving a self-contained algebraic solution, you are
*re-packaging* the analytic one.

### 7d. Go / no-go

- **GO** — for landing the **statements and definitions** of the adelic model as
  a documented, well-typed alternative. This is largely already done
  (Repartitions/H1/RiemannRochSpace are sorry-free); finishing the *definitional*
  reconciliation (L1.1 field structure, L1.5 places-as-HeightOneSpectrum) is
  worthwhile, moderate, and de-risks any later attempt.
- **GO** — for **road b-import** as a pragmatic way to *discharge the three
  `RiemannRochAnchor` sorries*, IF the goal is "make the adelic anchor a theorem"
  rather than "give a tower-free solution". ~1.8k lines, moderate difficulty,
  honest about its analytic dependency. This is the recommended next concrete
  step if anyone wants the anchor closed.
- **NO-GO (as a *cheaper* alternative to the existing analytic tree)** — for the
  FOUNDATIONS §4 thesis that route (b) is the *minimal* solution. The analytic
  Riemann–Roch (`riemannRochL3`, `serreDualityL3`, §5/§Layer3) is **already a
  sorry-free theorem on the critical path** (Jacobians/Layer3/Cohomology.lean:181,
  195, 0 sorries) backed by the keystone-flipped `H1coh`. Replacing it with a
  *self-contained* adelic proof (road b-trace) means building two Mathlib-absent
  research-grade edifices (removable singularities in branch-locus form; the
  algebraic differentials trace map) — strictly more work than the analytic proof
  the tree already owns.

### 7e. Named hard spots (one line each)

1. **L1.4 — trdeg-1 / `[K(X):ℂ(f)] < ∞`** — needs a degree theory for the cover
   *and* the Riemann removable-singularity theorem across the branch locus
   (Mathlib-absent). HARD / research-grade.
2. **L2.3/L2.5 — the algebraic trace map on differentials** for Serre
   nondegeneracy — no Mathlib API for Kähler differentials / trace on
   function-field extensions. RESEARCH-GRADE.
3. **B1 — the Riemann inequality is not bootstrappable inside the adeles** from
   the residue theorem alone; it must be imported (keeping the tower) or proven
   via the trace (walls 1–2). The single most important structural fact in this
   scope.
4. **L1.1 — `K(X)` is only a `CommGroup` in-tree**; the additive `Field`
   structure (and reconciliation with the separate `MeroField` quotient) is
   unbuilt prerequisite plumbing. MODERATE but unbudgeted in §4.

---

*References (all in-tree unless marked Mathlib): seed —
`vendor/kirov-dolbeault-port/.../FineResidue/SignTest.lean`,
`.../SerreResidueRamifiedRealSlitGeometry.lean:1017`,
`.../AbelSubsetEngineArc.lean:2133`, `.../SerreOmega0.lean:129`; Layer 1 —
`Jacobians/RiemannSurface/MeromorphicFunctionField.lean`,
`Jacobians/RiemannSurface/MeromorphicToP1.lean`; Layer 2 —
`Jacobians/RiemannSurface/Cohomology/{Repartitions,H1,RiemannRochSpace,
RiemannRochAnchor}.lean`; Layer 3 —
`Jacobians/RiemannSurface/PeriodDiscretenessKirovRoute.lean`,
`Jacobians/Axioms/AbelTheorem.lean`, `Jacobians/Layer3/Cohomology.lean`;
Mathlib — `RingTheory/DedekindDomain/{FiniteAdeleRing,AdicValuation,
Different,Ideal/Lemmas}.lean`, `NumberTheory/FunctionField.lean`,
`AlgebraicGeometry/FunctionField.lean`. External review: Gemini 3 Pro chat,
2026-06-12 (§6). Cross-refs: `docs/FOUNDATIONS.md` §4/§4½,
`docs/planning/KIROV_214_STUDY.md`.*

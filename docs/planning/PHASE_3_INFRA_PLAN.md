# Phase-3+ infrastructure plan: sheaf cohomology & the plane-curve atlas

*2026-06-04. Companion to [`ROADMAP.md`](ROADMAP.md), [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md), and [`../../DEFINITIONS_AUDIT.md`](../../DEFINITIONS_AUDIT.md).*

The cheap Phase-3 prerequisite-type discharges (`Hyperelliptic`, `infinityChart`)
are well-scoped and in progress. This document is the **real plan** for the two
remaining `needs-infra` clusters — the ones a one-line `def` cannot honestly
close:

- **Cluster A — sheaf cohomology** (`LineBundle`, `H0`, `H1`,
  `PrincipalDivisors`, `canonicalDivisor`, `LineBundle.ofDivisor`, + the
  `H0/H1` instance axioms): the ℂ-vector-spaces `H⁰(X,𝒪(D))`, `H¹(X,𝒪(D))` of a
  divisor on a compact Riemann surface. ~10 axioms.
- **Cluster B — the plane-curve atlas** (`PlaneCurve` + 7 instances + 3 affine
  props): the smooth projective plane curve `{F=0}⊂ℙ²` as a complex 1-manifold.
  ~11 axioms.

> **Headline verdict.** The existing per-axiom recipes propose a *token
> discharge* (`LineBundle D := PUnit`; `H0/H1` from `(sheafOfDivisor D).H n`).
> **That route, as written, is a faithfulness-wall failure, not a discharge** —
> see §A.2. The honest options are (i) leave Cluster A as **classified axioms**
> (its current, correct state), or (ii) commit to a multi-month real build. It
> is **not** a quick win, and we should not trade an honest axiom for a
> degenerate definition merely to lower a count. Cluster B is different: the
> *type* is faithfully and cheaply definable; only its *atlas* is `needs-infra`.

---

## A. Sheaf-cohomology cluster

### A.1 What Mathlib actually has (current pin, verified)

| Piece | Module | Usable? |
|---|---|---|
| Derived-functor sheaf cohomology `Sheaf.H F n` | `CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}` | **`AddCommGrpCat`-valued only**; `H F n := Ext` from constant ℤ-sheaf; `H.equiv₀ : H F 0 ≃+ Γ(T,F)` |
| Meromorphic order | `Analysis/Meromorphic/{Order,NormalForm}` (`meromorphicOrderAt`) | yes — gives `div f` pointwise |
| Nevanlinna / value distribution | `Analysis/Complex/ValueDistribution/*`, `JensenFormula` | tangential |
| `Divisor X` (ours) | `RiemannSurface/LineBundle.lean` = `FreeAbelianGroup X` (Phase 1) | yes, real |
| 𝒪(D) sheaf, Čech↔derived comparison, Cartan–Serre finiteness | — | **absent** |

### A.2 Why the proposed token discharge is *not* faithful

The recipes (`LineBundle.md`, `H0.md`, `H1.md`) propose:
`LineBundle D := PUnit`, `H0 _L := (sheafOfDivisor D).val.obj (op ⊤)`,
`H1 _L := (sheafOfDivisor D).H 1`. Three concrete defects:

1. **Type mismatch in `Sheaf.H`.** Mathlib's `Sheaf.H` is defined only for
   `F : Sheaf J AddCommGrpCat` (abelian groups), as `Ext`-groups from the
   constant ℤ-sheaf. `sheafOfDivisor D` would need to be `ModuleCat ℂ`-valued to
   carry the ℂ-structure the API (`H1.instModule`) demands — and there is **no
   ℂ-module-valued sheaf cohomology** in Mathlib. Recovering a faithful
   `Module ℂ` (and its `finrank`) from the `AddCommGrp`-valued `Ext` is itself a
   construction, not `inferInstance`.
2. **Dimension is unverified.** The *content* of the cluster is that
   `finrank ℂ (H0) − finrank ℂ (H1) = deg D + 1 − g` (Riemann–Roch) and Serre
   duality. The abstract derived-functor `H¹` is **not known to equal** the
   analytic `h¹(X,𝒪(D))` without a **comparison theorem** (derived = Čech =
   Dolbeault) that Mathlib lacks. A `def` that typechecks but whose `finrank` is
   unverified makes `AX_RiemannRoch`/`AX_SerreDuality` *vacuous about it* — the
   exact failure mode [`DEFINITIONS_AUDIT.md`](../../DEFINITIONS_AUDIT.md)
   defends against.
3. **The `H0.md` "minimal-carrier stub" (`H0 := ℂ`/`PUnit`) is openly
   degenerate** — its own recipe says it "would silently lose proof-relevance
   for actual meromorphic functions." That is a placeholder, not a discharge.

**Conclusion.** Replacing `axiom H1 : Type` with `def H1 := (…).H 1` *lowers the
axiom count while lowering faithfulness*. Per the project's stated philosophy
("axioms are classified, not hidden"), an honest `axiom H1` with a construction
plan is **strictly better** than a degenerate `def`. **Recommendation: keep
Cluster A as classified axioms unless we fund the real build below.**

### A.3 The real build (if pursued) — honest decomposition

A faithful Cluster A is a research-grade formalization. Ordered sub-tasks, each
a prerequisite for the next:

1. **`sheafOfDivisor D : Sheaf (ModuleCat ℂ) (Opens X)`** — the 𝒪(D) sheaf:
   `U ↦ { f meromorphic on U // ∀ p∈U, meromorphicOrderAt f p + D p ≥ 0 }`.
   Hard sub-lemmas: (a) the order constraint is a sub-ℂ-module of meromorphic
   functions; (b) the restriction maps + **sheaf gluing condition**; (c) the
   `ModuleCat ℂ` packaging. *~weeks; needs meromorphic-functions-on-a-manifold
   API we partly lack (Mathlib's meromorphic theory is local/ℂ-domain).*
2. **ℂ-module-valued cohomology.** Either (a) port `Sheaf.H` to `ModuleCat ℂ`
   (generalize Joël Riou's `Ext`-construction over a ℂ-linear base), or (b) take
   `Sheaf.H (forget₂ to AddCommGrp)` and *reconstruct* the ℂ-action — both real
   category-theory work.
3. **Faithful dimension.** Prove `H¹_derived ≅ H¹_Čech` over a finite Leray cover
   by charts (Mathlib has `SheafCohomology.Cech`), giving a *computable*
   finite-dimensional model whose `finrank` can be related to Riemann–Roch.
   *This is the crux and the longest pole.*
4. **Cartan–Serre finiteness** `FiniteDimensional ℂ (H1 L)` — Čech complex +
   Montel (we already vendor Montel via Kirov). *~weeks.*

**Honest estimate:** 2–4 months of focused formalization, much of it genuinely
new Mathlib-grade analysis/geometry. Recalibrated against the project's pace
(sister-project speedups apply only where infra exists — here it largely does
not).

### A.4 Recommendation for Cluster A

- **Default: leave as classified axioms.** They are correctly typed, citable
  (Forster Ch. II §16; Mumford), and already carry construction plans. This is
  the faithful choice.
- **If pursued:** treat **`sheafOfDivisor D` (A.3.1)** as a standalone milestone
  with its own PR and a non-vacuity witness (e.g. `H0 (𝒪(0)) ≅ ℂ` — global
  holomorphic functions on a compact connected RS are constants; we already have
  the Liouville machinery for this). **Do not** land `H0/H1` defs without that
  witness — it is the test that separates a faithful build from a token.

---

## B. Plane-curve cluster

Unlike Cluster A, the **type is faithfully and cheaply definable**; only the
manifold atlas is `needs-infra`. Split accordingly.

### B.1 Tier 1 — the type + topology (faithful, ~hours, DO)

`PlaneCurve.md` is right that the type is a real subtype:
```lean
def PlaneCurve (H : PlaneCurveData) : Type :=
  { p : Projectivization ℂ (Fin 3 → ℂ) // MvPolynomial.eval p.rep H.F.val = 0 }
```
This is **faithful** (the actual zero locus in ℙ²) — not a token. From it:
- `instTopologicalSpace`, `T2Space`, `CompactSpace`, `ConnectedSpace`,
  `Nonempty` should follow as a subtype of `Projectivization ℂ (Fin 3 → ℂ)`
  (compact Hausdorff; connectivity needs the curve irreducible — from
  `PlaneCurveData`'s smoothness/irreducibility hypothesis). *Caveat:* verify
  `Projectivization.rep` evaluation is well-defined on `MvPolynomial` (homogeneous
  `F` ⇒ the zero condition is rep-independent) — the recipe's `eval p.rep` needs
  a homogeneity lemma so the subtype is well-defined; **this is the one real
  obligation in Tier 1** and must be discharged, not assumed.
- **Discharges ~6 axioms** (type + 5 topological instances). Worth doing.

### B.2 Tier 2 — the three-chart atlas (`needs-infra`, weeks)

`ChartedSpace ℂ (PlaneCurve H)` + `IsManifold 𝓘(ℂ,ℂ) ω` via the three affine
charts `z≠0`, `y≠0`, `x≠0`, each `{f(x,y)=0}` made a chart by the **holomorphic
implicit function theorem** at a smooth point (`∂f/∂y ≠ 0` ⇒ local graph
`y=g(x)`). We have an IFT axiom (`GeneralResults/InverseFunctionTheorem.lean`)
and the Hyperelliptic atlas as a template. Sub-tasks:
1. Smoothness ⇒ at each point one partial is nonzero (covering the curve by the
   three charts). 2. IFT local graph chart. 3. Holomorphic transition maps on
   overlaps. 4. Glue (Mathlib `ChartedSpace` from an atlas of local homeos — same
   pattern as `Vendor/Kirov/ChartedSpaceOfLocalHomeomorph`). *Comparable to the
   Hyperelliptic odd/even atlas effort: weeks, but with an existing template.*

### B.3 The 3 affine props + Plücker genus

`AX_PlaneCurveAffine_connected/_noncompact/_nonempty` ride on Tier 1/2.
`AX_PluckerFormula` (`genus = (d−1)(d−2)/2`) stays a **Class-1 textbook axiom**
(it needs the full Riemann–Hurwitz/adjunction machinery — out of scope, like
Riemann–Roch).

### B.4 Recommendation for Cluster B

- **Do Tier 1 now** (faithful type + topology, ~6 axioms, after the homogeneity
  lemma). High value, honest, cheap.
- **Tier 2 atlas** is a real but *templated* multi-week task — schedule it as the
  successor to the Hyperelliptic atlas (`instChartedSpace`/`instIsManifold`),
  sharing the chart-gluing infrastructure.

---

## C. Sequencing & the faithfulness guardrail

1. **Now (in flight):** `Hyperelliptic` type + `infinityChart` (cheap, faithful).
2. **Next cheap+faithful:** PlaneCurve Tier 1 (§B.1) — gated on the homogeneity
   lemma.
3. **Real infra, scheduled (not "quick"):** Hyperelliptic + PlaneCurve atlases
   (share gluing infra); then `sheafOfDivisor D` (A.3.1) as the gateway milestone
   to Cluster A — with the `H0(𝒪(0))≅ℂ` non-vacuity witness as its acceptance
   test.
4. **Stay axioms (research-grade / textbook):** Riemann–Roch, Serre duality,
   Plücker, Cartan–Serre finiteness, the full Cluster-A dimensions until A.3 is
   funded.

**Guardrail (binding):** no `H0`/`H1`/`LineBundle`/`PlaneCurve`-atlas `def` lands
without a non-vacuity/faithfulness witness (the `localOrder_pow` pattern). A
discharge that lowers the axiom count but cannot exhibit such a witness is a
regression, not progress — it must be reviewed against
[`DEFINITIONS_AUDIT.md`](../../DEFINITIONS_AUDIT.md) before merge.

**The acceptance test is now machine-checkable.** For the sheaf-cohomology
cluster specifically, the faithfulness gate is the suite in
[`Jacobians/RiemannSurface/SheafCohomologySpec.lean`](../../Jacobians/RiemannSurface/SheafCohomologySpec.lean)
— Buzzard's anti-degeneracy strategy applied one layer down: non-vacuity anchors
(`H⁰(𝒪(0)) ≅ ℂ`, `H⁰=0` in negative degree, `H¹` vanishing), structural pins
(canonical degree `2g−2`, `H⁰(K) ≅ ℂ^g`, section monotonicity), and **concrete
ℙ¹ teeth** (`H⁰(𝒪(n·p)) ≅ ℂ^{n+1}`) that a token/degenerate definition provably
fails. The statements compile against the current axiom API (well-formedness
checked); a discharge of Cluster A is **accepted as faithful iff it turns
`SheafCohomologySpec.SheafCohomologyFaithful` into a theorem.** Land the concrete
§3 targets first — they are the discriminating ones.

*A Gemini deep-think consult on the `Sheaf.H` viability / dimension-faithfulness
was initiated (timed out at 5 min; interaction saved) — the §A.2 verdict is from
direct Mathlib API inspection and stands on its own; revisit Gemini to
pressure-test A.3 before funding it.*

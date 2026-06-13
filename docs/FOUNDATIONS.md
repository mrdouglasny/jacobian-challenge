# Foundational choices, and a minimal algebraic alternative

*A design retrospective for the jacobian-challenge formalization. Written 2026-06-13,
grounded in measured line counts and kernel-verified facts from the tree at that date.*

This document answers a question that is easy to ask and surprisingly subtle:
**how much of this formalization was forced by the problem, and how much was a
choice we made?** The repository contains, among other things, a ~127,000-line
"Dolbeault port" of complex-analytic machinery. Was all of that necessary? Could
the same challenge have been met "algebraically," with far less analysis?

The short answer is: **a small, irreducible amount of analysis is genuinely
forced — on the order of a thousand new lines — and almost everything else was a
choice about how to package the rest.** This document explains why, and then
sketches the leanest design the same challenge would admit.

Throughout, "the challenge" means Kevin Buzzard's Jacobian Challenge: fill in a
fixed Lean interface (24 `sorry`s) describing the Jacobian of a compact Riemann
surface, the Abel–Jacobi map, genus, and pushforward/pullback functoriality, and
prove the headline non-degeneracy facts (correct genus; injective Abel–Jacobi in
positive genus).

---

## 0. The problem statement makes the hardest decision for you

The single most important fact about this challenge is **how its objects are
defined**. Buzzard's interface is stated about **compact Riemann surfaces** —
that is, compact complex 1-dimensional *manifolds*, given to you as
`ChartedSpace ℂ X` with a complex manifold structure. It is **not** stated about
*smooth projective algebraic curves over ℂ*.

Those two notions describe the same mathematical objects (every compact Riemann
surface is an algebraic curve and vice versa), but they are *presented*
completely differently, and the presentation decides what tools you may use:

- If a curve is handed to you **algebraically** — as a projective variety, or via
  its field of rational functions — then Riemann–Roch and Serre duality are
  theorems of **commutative algebra**. You work with the function field, its
  valuations (one per point), divisors, and the residue pairing. No analysis, no
  limits, no integrals are required at any step.

- If a curve is handed to you **analytically** — as an abstract complex manifold,
  which is exactly Buzzard's setup — then you do not yet *have* a function field.
  You must **manufacture** one: you must first prove that the surface carries
  enough non-constant meromorphic functions to do algebra with. And **that
  existence statement is a deep analytic theorem.** There is no algebraic proof
  that an abstractly-given compact complex 1-manifold has *any* non-constant
  meromorphic function at all; producing them is the content of the classical
  existence theorems (Riemann's existence theorem, the Hodge/Dirichlet theory,
  or — equivalently — the solvability of the equation `∂̄u = f`).

So the irreducible analytic difficulty is not in Riemann–Roch. It is in the
**bridge from "analytic object" to "thing algebra can chew on,"** and that bridge
is forced by the problem's own definition of its objects. Had the challenge
defined curves algebraically, the entire Dolbeault apparatus in this repository
could be deleted. It did not, so it cannot.

This is worth stating plainly because it reframes everything that follows: the
expensive analysis is not a detour we could have routed around. A specific,
small piece of it is the price of admission.

---

## 1. The seed: the irreducible analytic core

Every analytic fact in this repository grows from **one classical lemma**: the
**inhomogeneous Cauchy formula**, also called the **Cauchy–Pompeiu formula**.

To state it, recall the Wirtinger operator `∂̄ = ½(∂/∂x + i ∂/∂y)`, which
measures how far a function is from being holomorphic (a function is holomorphic
exactly when `∂̄f = 0`). The lemma, as formalized here, is the single identity

> `∫_ℂ ∂̄(χ · (z − a)⁻¹) dA = −π · χ(a)`

(in `vendor/.../FineResidue/SignTest.lean`, resting on `DbarDisk.cauchyPompeiu_area`).
Here `χ` is any smooth, compactly supported test function, `a` is a point, `dA`
is Lebesgue *area* measure on `ℂ`, and `(z − a)⁻¹` is the one-variable Cauchy
kernel. In words: integrating `∂̄` of "a bump times the pole `1/(z−a)`" against
area picks out the value of the bump at the pole, up to the constant `−π`.

This little identity is the seed from which the two facts that the *entire rest*
of the challenge needs both grow:

1. **The residue theorem** — `∑ Res = 0` for a meromorphic differential on the
   compact surface. Residues are local, the sum is global, and the bridge
   between them is exactly the Cauchy–Pompeiu atom applied chart by chart.

2. **`∂̄`-solvability** — the existence of meromorphic functions with prescribed
   singularities (formalized through `exists_meromorphic_of_zeroPeriodChain'`).
   This is the analytic existence theorem of §0: it is what lets you build the
   function field and cross over to algebra.

These two — the residue theorem and `∂̄`-solvability — are the *whole* analytic
content the challenge requires. Everything else is algebra, linear algebra, or a
choice about how to package those two facts.

### How big is the seed, really?

Measured from the port's Lean source (excluding build artifacts; 2026-06-13):

| Layer | Lines | Honest status |
|---|---:|---|
| Cauchy–Pompeiu atom (`DbarDisk` + `SignTest`) | ~970 | the irreducible seed |
| `FineResidue/` — the residue calculus built on the atom | ~7,700 | mostly necessary |
| `SerreResidue*` — the residue theorem + ramified-cover trace apparatus | ~15,400 | partly packaging |
| **Čech / sheaf-cohomology tower** — Riemann–Roch the long way | ~35,200 | **the over-build** |
| whole Dolbeault port (source `.lean`) | 127,619 | — |

Two things stand out.

**First, the conceptually-new content is tiny — about a thousand lines.** And
even that thousand lines rests almost entirely on **machinery Mathlib already
had**: Cauchy's integral theorem (Cauchy–Goursat), the Wirtinger calculus, and
Lebesgue measure theory. The genuinely *new*, Riemann-surface-specific analytic
work is a few hundred lines of wiring Mathlib's one-variable complex analysis
into the area-integral form above. The hard theorem underneath — Cauchy's
theorem itself — was formalized in Mathlib years ago, for everyone, long before
this challenge existed. **The seed was cheap because the giants were already
standing.**

**Second, the bulk of the 127,000 lines is not the seed.** It is the *tower built
over the seed* — and, as the next section argues, a large part of that tower was
optional.

---

## 2. The first big choice: prove Riemann–Roch analytically, or algebraically?

Once you have the seed (the residue theorem and `∂̄`-solvability), **Riemann–Roch,
Serre duality, and Abel's theorem can be obtained in either of two styles**, and
the styles have very different costs:

- **The analytic style** builds sheaf cohomology directly: Čech `H¹`, the
  skyscraper long-exact-sequence, fine resolutions, the Dolbeault isomorphism.
  This is what the ~35,000-line cohomology tower in the port does. It is correct,
  self-contained, and it reaches `theorem` — but it is heavy.

- **The algebraic style** crosses to the function field and never looks back. It
  represents `H¹` using the **adele ring** of the function field (Weil's
  "repartitions"): `H¹(D) = A_K / (K + A_K(D))`, where `A_K` is the restricted
  product of the local fields at all points. Riemann–Roch becomes a dimension
  count in this quotient, and **Serre duality is the residue pairing**
  `(η, ω) ↦ ∑ Res(η ω)` — well-defined and non-degenerate *because of the seed's
  residue theorem*. This is pure commutative algebra sitting on top of Layer 0.

The repository chose the analytic style — not because the algebraic style was
unavailable, but because the analytic proof reached a sorry-free state first, and
once a result is a theorem there is little pressure to reprove it. This is
ordinary path-dependence, not a mistake.

But there is concrete evidence in the tree that the algebraic style was viable on
exactly the same seed:

- **`RiemannRochAnchor.lean` already implements it.** It is the Weil-repartition
  / adele model of `H¹` with Serre duality via the residue pairing — kept as a
  documented alternative, three `sorry`s from completion, never placed on the
  critical path. It is the algebraic packaging of Riemann–Roch, and it sits on
  the seed's residue theorem.

- **The endgame retroactively proved the lean pattern works.** When we finally
  closed the period-lattice and Abel sides of the challenge (the K-LITE work and
  the Abel-⊆ engine), those proofs consumed *only* the residue theorem and the
  `∂̄`-solvability engine — **not** the Čech tower at all. In other words, the
  hardest remaining parts of the challenge turned out to need just the small
  analytic core plus linear algebra. The 35,000-line cohomology tower was, in
  hindsight, the clearest single over-build: it proves through full sheaf
  cohomology what the seed plus adeles would have proved with far less.

---

## 3. The second big choice: how to build the Jacobian's period lattice

A second, independent foundational decision concerns the **Jacobian** itself —
and it is precisely where the formalization's last remaining axiom lived.

The Jacobian of a genus-`g` surface is a complex torus `ℂ^g / Λ`, where `Λ` is
the **period lattice**: the set of vectors `(∫_γ ω₁, …, ∫_γ ω_g)` you get by
integrating a basis of holomorphic 1-forms around closed loops `γ`. The question
is *how to construct `Λ`* — and there are two natural answers.

- **This repository's original answer** routes through topology. It builds `Λ`
  from the first homology group `H₁`, identifying `H₁` with the *abelianized
  fundamental group* and using a **chosen basis of cycles** to extend the
  "integrate around this loop" map linearly over all of `H₁`. Concretely,
  `loopIntegralToH1` used `Module.Basis.constr` over a basis selected by
  `Classical.choice (AX_PeriodCycleBasis)`. The price of going through abelianized
  `π₁` and the Hurewicz map is exactly that cycle-basis axiom: the assertion that
  a nice `2g`-element symplectic basis of cycles exists, with all its bilinear
  (Riemann) relations.

- **Kirov's verified solution** (which we studied and adopted) takes the other
  road. It builds `Λ` **directly** as `span ℤ {periods of closed loops}` — no
  `H₁`, no Hurewicz tie, no chosen basis. That it is a genuine lattice of full
  rank `2g` then falls out of Mathlib's general theory of `ℤ`-lattices
  (`ZLattice`): a subgroup of `ℂ^g ≅ ℝ^{2g}` that is *discrete* and *spans over
  ℝ* is automatically free of rank `2g`. Notably, Kirov never built the classical
  "fundamental polygon / cut-surface" object at all — in his tree it is a `sorry`
  too — and he reached the lattice by the Forster §21.4 route instead. (We
  cloned and kernel-verified his leaderboard submission, commit `906335f`, and it
  is clean at the three standard axioms.)

The lesson is sharp. **Tying the Jacobian to abelianized `π₁` is mathematically
natural but costs a hard topology axiom.** Building it directly on the period
lattice costs only one thing: a proof that the lattice is *discrete*. And
discreteness, it turns out, follows from the seed alone (a non-zero lattice
vector that is "too small" produces, via `∂̄`-solvability, a meromorphic function
whose residues must cancel — a contradiction; this is the K-LITE argument).

The **K-FULL** refactor (owner-approved; see Discussion #235) adopts the
lattice-direct design without changing any of the challenge-facing statements:
it re-founds the period map on the **axiom-free** developing-value invariant
(`Abelianization.lift`, which extends over `H₁` functorially with *no* chosen
basis), so the cycle-basis axiom leaves the entire Jacobian construction. After
this refactor the `Jacobian` type, the Abel–Jacobi map, the genus, and the
genus-zero uniformization are all axiom-free; the lone surviving use of the axiom
is in the *injectivity* statement and reduces to a single named topology fact —
"analytic loops generate `H₁`" — which is proven at genus 1 and concrete for the
explicit curve families.

---

## 4. A minimal algebraic solution (the lean counterfactual)

Putting the three observations together — the analytic seed is forced and small;
Riemann–Roch can be algebraic; the Jacobian can be lattice-direct — here is the
leanest design the same challenge admits. This is not a demand to rewrite the
working tree (which is sorry-free on the critical path and externally
comparator-verified); it is a map of where the weight genuinely *has* to go.

### Layer 0 — the analytic seed *(irreducible; ~1k new lines over Mathlib)*
1. The Wirtinger `∂̄` and the Cauchy–Pompeiu area atom, built from Mathlib's
   Cauchy theory.
2. The residue theorem `∑ Res = 0`.
3. `∂̄`-solvability on the compact surface ⇒ **existence of non-constant
   meromorphic functions** — the analytic bridge of §0.

### Layer 1 — cross over to algebra *(small in code; conceptually the crux)*
4. From step 3, assemble the meromorphic function field `K(X)` (transcendence
   degree 1 over ℂ); its points become *places*, its order-of-vanishing maps
   become *valuations*. This is the only step where analysis is essential; once
   `∂̄`-solvability is in hand, the formalization of the field is modest.

### Layer 2 — Riemann–Roch and Serre, algebraically *(replaces the ~35k Čech tower)*
5. Form the **adele ring** `A_K` and Weil repartitions; define `H¹(D) = A_K /
   (K + A_K(D))`. (The repo's `RiemannRochAnchor.lean` is exactly this, three
   `sorry`s from done.)
6. Riemann–Roch as the index `[A_K : K + A_K(D)]` count; finiteness of `H¹`;
   `h¹(𝒪) = g`.
7. **Serre duality** as the residue pairing `H¹(D) × H⁰(K−D) → ℂ`,
   `(η, ω) ↦ ∑ Res(η ω)`, with the seed's residue theorem supplying
   well-definedness and non-degeneracy. Commutative algebra over Layer 0.

### Layer 3 — the Jacobian and Abel, lattice-direct *(the K-FULL shape)*
8. The period lattice `Λ = span ℤ {∫_γ ω}` over closed loops; its discreteness
   from the seed (the K-LITE argument), its rank `2g` from `ZLattice`. **No
   cycle-basis axiom.**
9. `Jacobian = ℂ^g / Λ`; the Abel–Jacobi map `D ↦ (∫ ω)` into the quotient.
10. **Abel's theorem**, both directions, over Layer 0 plus the lattice: the "⊇"
    direction by a Liouville argument on the pencil `ℙ¹ → Jac` (the residue
    theorem plus simple-connectivity of `ℙ¹`); the "⊆" direction by the §20
    `∂̄`-solvability engine (Layer 0) feeding a chain whose vanishing periods
    bound a principal divisor.

### What this design buys, and what it cannot

It **drops the ~35,000-line Čech cohomology tower** (Layer 2 is algebraic) and
**drops the cycle-basis axiom** (Layer 3 is lattice-direct). The ramified-cover
trace machinery (`FormTrace*`, the slit geometry — tens of thousands of lines)
was needed only by the analytic Riemann–Roch proof, and it largely disappears
with it.

It **keeps the seed** (~1k new lines) and the period-lattice linear algebra,
because those are irreducible.

The one genuinely hard residual that *no* packaging removes is the **topology of
`H₁` of a general compact surface** — that it is finitely generated, free, and of
rank `2g`. But the lattice-direct design defers even this: it needs only the
lattice's *discreteness* (which the seed gives), and if one further insists on
the abelianized-`π₁` presentation, the remaining gap collapses to the single
statement **"analytic loops generate `H₁`"** — provable concretely for the
explicit curve families, and reducing the general case to one clean
covering-space lemma.

### Rough size budget

| Layer | Project-specific Lean (estimate) | vs. current tree |
|---|---|---|
| 0 — analytic seed | ~1k new (on Mathlib) | unchanged — irreducible |
| 1 — function field | small (statement is the crux) | new, modest |
| 2 — adelic RR/Serre | a few thousand | replaces ~35k Čech tower |
| 3 — lattice Jacobian + Abel | several thousand | replaces the cycle-basis axiom |

A focused implementation along these lines would plausibly come in **well under
20,000 lines of project-specific Lean** over Mathlib, against the ~127,000-line
vendored Dolbeault port — most of the saving coming from replacing the analytic
Riemann–Roch tower with algebra, and replacing the cycle-basis axiom with a
lattice-direct Jacobian.

---

## 5. The honest summary

- **The expensive thing was never the seed.** The irreducible analytic core is
  about a thousand new lines, and even those rest on complex-analysis machinery
  Mathlib already had. What cost the bulk of the ~127,000 lines was the *tower
  built over the seed* — proving Riemann–Roch and Serre duality through full
  Dolbeault sheaf cohomology, and tying the Jacobian to abelianized `π₁` — when
  an algebraic packaging plus a lattice-direct Jacobian would have needed
  neither.

- **Both heavy choices were reasonable, not errors.** They reached sorry-free
  `theorem` status, and the analytic Riemann–Roch tower is independently valuable
  formalization that the broader Lean ecosystem may want. But the *minimal* route
  to this particular challenge is: the seed, plus adelic Riemann–Roch/Serre, plus
  a lattice-direct Jacobian — which is, in retrospect, exactly the shape the
  endgame (K-LITE, the Abel engine, the K-FULL refactor) converged on under its
  own pressure.

- **The one irreducibly hard input is analytic and is forced by the problem's
  definition of its objects.** A compact Riemann surface, presented as an
  abstract complex manifold, must be *shown* to carry non-constant meromorphic
  functions — equivalently, `∂̄u = f` must be shown solvable. Everything else is
  algebra, linear algebra, or a choice of how to package them.

---

*References: `vendor/.../FineResidue/SignTest.lean` (the Cauchy–Pompeiu atom);
`Jacobians/RiemannSurface/Cohomology/RiemannRochAnchor.lean` (the in-tree adelic
route); `Jacobians/RiemannSurface/PeriodDiscretenessKirovRoute.lean` (K-LITE,
the lean pattern); `docs/planning/KIROV_214_STUDY.md`; Discussion #235 (K-FULL).*

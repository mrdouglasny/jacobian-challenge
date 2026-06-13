# Foundational choices, and a minimal algebraic alternative

*A design retrospective for the jacobian-challenge formalization. Written 2026-06-13,
grounded in measured line counts and kernel-verified facts from the tree at that date.*

This document explains **why the formalization is shaped the way it is** — which
choices were forced by the problem and which were genuinely optional — and then
sketches the **leanest algebraic solution** that the same goal would admit. It is
honest about what the heavy machinery bought and what it over-bought.

---

## 0. The problem fixes the hardest choice for you

Buzzard's challenge is stated about **compact Riemann surfaces** — complex
1-manifolds, *defined analytically* (`ChartedSpace ℂ X` + `IsManifold`). It is
not stated about smooth projective curves over ℂ. That single framing decision
is the source of essentially all the difficulty, because:

- For an **algebraically**-defined curve, Riemann–Roch and Serre duality are
  commutative algebra (function fields, valuations, the residue pairing on
  adeles). No analysis is needed.
- For an **analytically**-defined surface, you must first manufacture the
  algebra: produce nonconstant meromorphic functions, identify the function
  field, bridge analytic ↔ algebraic (the Riemann existence theorem / GAGA).
  **That bridge is itself a deep analytic theorem** — there is no algebraic
  proof that an abstractly-given compact complex 1-manifold carries any
  nonconstant meromorphic function. Its content is the solvability of `∂̄u = f`
  (equivalently Hodge/Dirichlet theory).

So the irreducible analytic input is forced by the *definition of the objects*,
not by Riemann–Roch. If the challenge had defined curves algebraically, the
entire Dolbeault apparatus could be skipped. It did not, so it cannot.

---

## 1. The seed: the irreducible analytic core

Everything analytic in this repository grows from one classical lemma — the
**inhomogeneous Cauchy (Cauchy–Pompeiu) formula**, formalized as the atom

> `∫_ℂ ∂̄(χ·(z − a)⁻¹) dA = −π·χ(a)`   (`FineResidue/SignTest.lean`, on `DbarDisk.cauchyPompeiu_area`)

against Lebesgue area on `ℂ`, with `∂̄` the Wirtinger operator. From this atom:

- the **residue theorem** `∑ Res = 0` (`residueTheorem_unconditional`), and
- **∂̄-solvability** on the compact surface (the existence of meromorphic
  functions with prescribed principal parts — `exists_meromorphic_of_zeroPeriodChain'`)

follow. These two facts are the *whole* analytic content the rest of the
challenge needs.

### Measured size (port source, excl. build artifacts; 2026-06-13)

| Layer | Lines | Status |
|---|---:|---|
| Cauchy–Pompeiu atom (`DbarDisk` + `SignTest`) | ~970 | the irreducible seed |
| `FineResidue/` (residue calculus on the atom) | ~7,700 | mostly necessary |
| `SerreResidue*` (residue theorem + ramified-cover trace) | ~15,400 | partly packaging |
| **Čech / cohomology tower** (RR/Serre the long way) | ~35,200 | **the over-build** |
| whole Dolbeault port (source `.lean`) | 127,619 | — |

**The conceptually-new content is ~1k lines.** Even the atom rests almost
entirely on **Mathlib's pre-existing complex analysis** — Cauchy–Goursat, the
Wirtinger calculus, Lebesgue measure theory. The genuinely-new, surface-specific
work is a few hundred lines wiring Mathlib's one-variable complex analysis into
the area-integral form. The heavy lifting (Cauchy's theorem itself) was done by
Mathlib years ago, for everyone, not for this challenge.

---

## 2. The choice: Dolbeault tower vs. algebraic packaging

Given the seed, **Riemann–Roch, Serre duality, and Abel's theorem can be
packaged either analytically or algebraically.** The repository chose the
analytic packaging (the full Čech / sheaf-cohomology Dolbeault tower) because it
reached `theorem` first. That was a path-dependence, not a necessity.

Evidence that the algebraic packaging was viable on the same seed:

- **`RiemannRochAnchor.lean` exists in-tree** — the Weil-repartition / adele
  model of `H¹`, with Serre duality via the residue pairing on adeles (3
  `sorry`s, kept as a documented alternative, never on the critical path). This
  is RR/Serre as commutative algebra over the seed's residue theorem.
- **The endgame retroactively validated the lean pattern.** The period-lattice
  discreteness (K-LITE, `PeriodDiscretenessKirovRoute.lean`) and the Abel-⊆
  engine consume *only* `residueTheorem_unconditional` + the ∂̄-solvability
  engine — **not** the Čech tower. The entire lattice/Abel half of the challenge
  ran on the small analytic core plus linear algebra.

So the ~35k-line Čech tower is the clearest over-build: it proves RR/Serre
through full sheaf cohomology where the seed + adeles would have sufficed.

---

## 3. The architecture choice: H₁-tied vs. lattice-direct Jacobian

A second, independent foundational choice concerns **how the Jacobian's period
lattice is built** — and it is the location of the last surviving axiom.

- **This repo (original):** the Jacobian is `ℂ^g / image(loopIntegralToH1)`,
  where `loopIntegralToH1` extends the period functional `ℤ`-linearly over
  `H₁ = Additive(Abelianization(π₁))` via a **chosen cycle basis**
  (`Module.Basis.constr` over `cb = Classical.choice (AX_PeriodCycleBasis)`).
  The cycle-basis axiom is the price of routing through abelianized `π₁` and the
  Hurewicz map.

- **Kirov's verified tree:** the Jacobian is built **directly on the period
  lattice** `span ℤ (closed-loop periods)` — no `H₁`, no Hurewicz tie, no cycle
  basis. Rank `2g` falls out of Mathlib's `ZLattice` theory (discrete +
  ℝ-spanning ⇒ free of rank `dim_ℝ ℂ^g`). He retired the cut-surface /
  fundamental-polygon construction entirely (his `exists_cutSurface` was never
  built — it is `sorry` in his tree too; he reached the lattice by the Forster
  21.4 route instead). We kernel-verified his leaderboard submission
  (`906335f`) is clean at standard-3.

The **K-FULL** refactor (owner-approved, Discussion #235; executing as
`feat/refound-periodmap`) adopts the lattice-direct design: re-found the period
map on the **axiom-free Hurewicz tower** `loopDevValH1Hom`
(`Abelianization.lift`, no basis), so `AX_PeriodCycleBasis` leaves the entire
Jacobian layer. Its discreteness/rank/basis are the K-LITE results
(unconditional, dissection-free). After this, the challenge's last axiom
survives only inside the Abel-⊆ engine's *generation* step, which reduces to
**T-GEN** (analytic loops generate H₁) — a single topology residual, proven at
genus 1, concrete for the witness families.

**Lesson:** tying the Jacobian to abelianized π₁ (mathematically natural) costs
a hard topology axiom; building it on the period lattice (Kirov's choice, now
ours) costs only the lattice's discreteness — which the seed already supplies.

---

## 4. A minimal algebraic solution (the lean counterfactual)

Putting §§1–3 together, here is the leanest design the same challenge admits.
It is not a critique that demands a rewrite — the current tree is sorry-free on
the critical path and externally comparator-verified — but a map of where the
weight actually had to go.

### Layer 0 — the analytic seed (irreducible, ~1k new LOC on Mathlib)
1. `∂̄`-Wirtinger + the Cauchy–Pompeiu area atom (from Mathlib's Cauchy theory).
2. The residue theorem `∑ Res = 0`.
3. `∂̄`-solvability on the compact surface ⇒ **existence of nonconstant
   meromorphic functions** (the analytic bridge to algebra).

### Layer 1 — cross to algebra (the function field)
4. From (3): the meromorphic function field `K(X)` (transcendence degree 1 over
   ℂ); places = points; valuations from orders of vanishing. This is the
   Riemann-existence content, and it is the *only* place analysis is essential.

### Layer 2 — Riemann–Roch & Serre, algebraically (replaces the ~35k Čech tower)
5. The **adele ring** `A_K` and Weil repartitions; `H¹(D) = A_K / (K + A_K(D))`.
   (The repo's `RiemannRochAnchor.lean` is this, 3 sorries from done.)
6. Riemann–Roch as the index `[A_K : K + A_K(D)]` computation; finiteness of
   `H¹`; `h¹(𝒪) = g`.
7. **Serre duality** via the residue pairing `H¹(D) × H⁰(K−D) → ℂ`, `(η, ω) ↦
   ∑ Res(ηω)` — using the seed's residue theorem for well-definedness and
   non-degeneracy. Pure commutative algebra over Layer 0.

### Layer 3 — the Jacobian & Abel, lattice-direct (the K-FULL shape)
8. Period lattice `Λ = span ℤ (∫_γ ω)` over closed loops; discreteness from the
   seed (a nonzero lattice point in an IFT window ⇒ a zero-period chain ⇒ a
   meromorphic function ⇒ residue contradiction — the K-LITE argument, which
   needs only Layer 0). Rank `2g` from `ZLattice`. **No cycle-basis axiom.**
9. `Jacobian = ℂ^g / Λ`; Abel–Jacobi `D ↦ (∫ ω)` into the quotient.
10. **Abel's theorem** both directions over Layer 0 + the period lattice: ⊇ by
    Liouville on the pencil `ℙ¹ → Jac` (the seed's residue theorem +
    simply-connected ℙ¹); ⊆ by the §20 ∂̄-solvability engine (Layer 0) feeding a
    chain whose zero periods bound a principal divisor.

### What this buys
- **Drops the ~35k Čech tower** (Layer 2 algebraic) and the cycle-basis axiom
  (Layer 3 lattice-direct). The trace / ramified-cover machinery (`FormTrace*`,
  the slit geometry, ~tens of k LOC) is needed only by the analytic RR proof and
  largely disappears.
- **Keeps the seed** (~1k new LOC) and the period-lattice linear algebra —
  irreducible.
- The one genuinely-hard residual that *no* packaging removes is the topology of
  `H₁` of a general compact surface (finite generation, rank `2g`, torsion-free)
  — but the lattice-direct design (Layer 3) reduces even this to the lattice's
  discreteness, which the seed supplies, leaving only **T-GEN** if one insists on
  the abelianized-π₁ presentation.

### Rough size
- Layer 0: ~1k new (on Mathlib's complex analysis).
- Layer 1: small, but the *statement* of Riemann existence is the conceptual
  crux; the formalization is modest once `∂̄`-solvability is in hand.
- Layer 2: the adele/RR/Serre algebra — call it a few thousand LOC, vs ~35k for
  the Čech route.
- Layer 3: the period lattice + Abel — the K-LITE + Abel-engine work, ~several k.

A focused implementation along these lines would plausibly be **well under
20k LOC of project-specific Lean** over Mathlib, against the ~127k vendored
Dolbeault port — most of the saving from replacing the analytic RR/Serre tower
with algebra and the cycle-basis axiom with the lattice-direct Jacobian.

---

## 5. Honest summary

- The **expensive thing was never the seed** (~1k irreducible LOC, mostly
  Mathlib underneath). It was the **tower built over it** — proving RR/Serre
  through full Dolbeault sheaf cohomology, and tying the Jacobian to abelianized
  π₁, when the algebraic/lattice-direct packaging needed neither.
- Both heavy choices were **reasonable path-dependence**, not error: they reached
  sorry-free `theorem` status, and the analytic RR tower is independently
  valuable formalization. But the *minimal* route to the same challenge is the
  seed + adelic RR/Serre + a lattice-direct Jacobian — which is, in retrospect,
  exactly the shape the endgame (K-LITE, the Abel engine, K-FULL) converged on.
- The single irreducibly-hard input is analytic and forced by the problem's
  definition of its objects: **a compact Riemann surface has nonconstant
  meromorphic functions** — `∂̄u = f` is solvable. Everything else is algebra,
  linear algebra, or a choice of how to package them.

*References: `FineResidue/SignTest.lean` (the atom), `RiemannRochAnchor.lean`
(the in-tree adelic route), `PeriodDiscretenessKirovRoute.lean` (K-LITE / the
lean pattern), `docs/planning/KIROV_214_STUDY.md`, Discussion #235 (K-FULL).*

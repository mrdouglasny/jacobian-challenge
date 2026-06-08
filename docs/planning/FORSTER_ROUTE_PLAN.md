# Forster-route discharge plan for the core period axioms

**Thesis.** Re-base the discharge of the core Jacobian axioms on Forster's
cohomological route (GTM 81, Ch. 2) instead of the Griffiths–Harris Hodge /
period-matrix route the current `AX_*` plans assume. The Forster route's single
hard analytic input — the §14 finiteness theorem — **is already discharged in
this project** via the vendored Kirov Montel machinery, and everything else is
homological algebra that avoids the 4g-gon topology and polygon-Stokes (the two
biggest, not-in-Mathlib line items of the current plans).

Companion: [`JACOBIAN_ROUTE_COMPARISON.md`](JACOBIAN_ROUTE_COMPARISON.md) (the
route comparison + prereq trees).

---

## 0. What we already have (the keystone is done)

The one hard analytic prerequisite of Forster's route is **§14: finiteness of
`H¹(X, O)`**, equivalently (by Serre, §17.10) **`dim H⁰(X, Ω¹) < ∞`**. The
project already has this:

- `Jacobians/Axioms/FiniteDimOneForms.lean` — the old `AX_FiniteDimOneForms`
  axiom was **retired 2026-04-25**. `FiniteDimensional ℂ (HolomorphicOneForm X)`
  is now a **theorem**, transferred from Kirov's real Montel-derived
  `FiniteDimensional ℂ (Vendor.Kirov.HolomorphicOneForms X)` along an injective
  ℂ-linear bridge (`Jacobians/Bridge/KirovHolomorphic.lean`), modulo two
  *mechanical* bridge axioms (`bridgeForm` exists / is injective).
- `Jacobians/Vendor/Kirov/Montel/{Compactness,Complete,Cover,LocalRep,ChartNorm,
  SupNorm,ChartTransition}.lean` — a full normal-families / Montel compactness
  layer. This is exactly the analytic engine §14 runs on.

So the deepest step of Route 1 is essentially banked. Forster as literally
written wants `dim H¹(X,O) < ∞`; we hold the Serre-dual form `dim H⁰(Ω¹) < ∞`.
Either seeds Ch. 2 — see §2 below for which to standardize on.

Other existing scaffolding to connect to:
- `Jacobians/RiemannSurface/Cohomology/{H1,Repartitions,RiemannRochAnchor}.lean`
  — the cohomology layer (Weil-repartition / adelic anchor, from PR #105).
- `Jacobians/RiemannSurface/{RiemannRochAPI,SerreDualityAPI}.lean` — the vetted
  RR/Serre statement anchors (8 deferred sorries — the "Wall A" frontier).
- `Jacobians/RiemannSurface/HolomorphicOneForm`, `Genus.lean`, `PathIntegral.lean`
  (`loopIntegralToH1`, already proven), `AnalyticArc.lean`.

## 1. Axioms this route targets

| Axiom | File | Forster discharge |
|-------|------|-------------------|
| `AX_RiemannRoch` | `Axioms/RiemannRoch.lean:59` | §16, from §14 finiteness + §15 exact sequence |
| `AX_SerreDuality` | `Axioms/SerreDuality.lean:54` | §17, from §16 + residues |
| `AX_RiemannBilinear` | `Axioms/RiemannBilinear.lean:69` | **off the critical path for the torus** — Route 1 reaches the period lattice without it (§3). BUT still required later for the **principal polarization / algebraicity** (Gemini C1 below): Forster builds only a complex torus, not a polarized abelian variety. |
| `AX_AnalyticCycleBasis` | `Axioms/AnalyticCycleBasis.lean:265` | **only the rank part is free.** Forster gives `H₁ ≅ ℤ^{2g}` as an abstract free group (§21.5), no 4g-gon — but **not** the symplectic basis or the intersection pairing (Gemini C1). The `loops_to_basis` / symplectic content + `AX_IntersectionForm` still need intersection theory / bilinear relations. |
| `AX_PeriodLattice` (+ `instPeriodLatticeDiscrete`) | `Axioms/PeriodLattice.lean:92` | §21.4 directly, from `dim Ω¹ = g` + Abel |
| `RiemannRochAPI`/`SerreDualityAPI` sorries (Wall A) | `RiemannSurface/*API.lean` | become the *main line*, not a side wall |

The payoff is structural: in Route 1 the **construction of `Jac(X)` as a complex
torus** and the **full-rank period lattice** do not require the two heaviest items
(`AX_AnalyticCycleBasis`'s 4g-gon, `AX_RiemannBilinear`'s polygon-Stokes —
combined plan estimate well over a year). `H₁ ≅ ℤ^{2g}` (as an abstract free
group) is *derived* (§21.5), not assumed. **Caveat (Gemini C1):** Forster does
**not** derive the symplectic basis or intersection pairing, and stops at a
complex torus — the intersection form / Riemann bilinear relations return *if and
when* we need the **principal polarization (algebraicity)** of the Jacobian. So
the win is "construct the torus + lattice cheaply"; the polarization is deferred,
not eliminated.

## 2. Build order (each step cites Forster + the file it lands in)

1. **Standardize the finiteness keystone.** Decide between (a) keep `dim H⁰(Ω¹)
   < ∞` (have it) and adapt §16–17 to start from the 1-form side, or (b) prove
   `dim H¹(X,O) < ∞` directly with the same Montel engine. Recommend (a):
   reuse `Bridge/KirovHolomorphic.lean`; only the two mechanical bridge axioms
   remain. → consolidate in a new `RiemannSurface/Cohomology/Finiteness.lean`.
2. **Čech `H¹(X,O)` + Dolbeault.** Forster §12–13. We have an `H1` type
   (`Cohomology/H1.lean`); need the structure-sheaf cohomology + the
   local-`∂̄`-solvability lemma (Dolbeault, §13). This is the main genuinely-new
   analytic lemma; it is local and standard.
3. **Exact sequence + deRham** (§15) → `Cohomology/ExactSequence.lean`.
4. **Riemann–Roch** (§16.9) — discharges `AX_RiemannRoch`. Pure homological
   algebra over steps 1–3. Land in `Axioms/RiemannRoch.lean` (axiom → theorem),
   retiring the `RiemannRochAPI` sorries it covers.
5. **Serre duality** (§17.9) + the corollary **`dim H⁰(Ω¹) = g`** (§17.10) —
   discharges `AX_SerreDuality`, retires `SerreDualityAPI` sorries.
6. **Harmonic forms / Hodge decomposition** (§19) *as a corollary* of 5 +
   Dolbeault. The `⋆`-operator and `⟨ω,η⟩=∫ω∧⋆ω` positivity are elementary
   (`19.5`). → `RiemannSurface/HarmonicForms.lean`.
7. **Abel's theorem** (§20) — uses 5, 6, surface-Stokes. → `Axioms/AbelTheorem.lean`
   (relate to existing `AX_AbelTheorem`).
8. **Period lattice + Jacobi inversion** (§21) — `Per(ω₁,…,ω_g)` is a lattice in
   ℂ^g (§21.4) and `H₁ ≅ ℤ^{2g}` (§21.5, as an abstract free group). Discharges
   `AX_PeriodLattice`, `instPeriodLatticeDiscrete`, and **provides the *rank* part
   of `AX_AnalyticCycleBasis`** (the symplectic basis + intersection pairing are
   NOT produced here — Gemini C1). → `Axioms/PeriodLattice.lean`,
   `Axioms/AnalyticCycleBasis.lean`.

## 3. Why `AX_RiemannBilinear` drops out

The current `AX_PeriodLattice` plan derives lattice-fullness from the bilinear
relations (`Im τ ≻ 0` ⇒ the `2g` period vectors are ℝ-independent), which is why
it needs the Hodge norm + polygon-Stokes. Forster §21.4 instead proves
`Per(ω₁,…,ω_g)` is a lattice *directly*:
- **discreteness / `Γ∩W=0`** from Abel's theorem + the residue theorem (§21.4b),
- **spanning** from the harmonic-period nondegeneracy corollary (§19.8, §21.4c),
- **rank-`g` period matrix** from `dim Ω¹ = g` (§17.10).

None of these is the bilinear-relations period matrix. So `AX_RiemannBilinear`
is not on the critical path for **constructing the torus and proving the lattice
is full-rank**. It remains required for the **principal polarization** (the
`Im τ ≻ 0` positivity that makes `Jac(X)` a projective abelian variety, not just
a complex torus) — see Gemini C1. For the bare challenge + Albanese (which are
torus-level), the period lattice no longer waits on it; for algebraicity, it
returns.

## 3b. Gemini deep-think review (2026-06-07)

Vetted the route claims (full prompt + verdicts archived with the session).
Summary:
- **C2 / C3 / C4 / C5: Correct.** No hidden prerequisites. Forster genuinely
  avoids polygon-Stokes, the Hodge-norm-as-a-separate-theorem, elliptic
  regularity (Sobolev/Laplacian), *and* triangulations. Full-rank **spanning**
  uses the **maximum principle** (a non-zero harmonic form with all periods zero
  integrates to a non-constant harmonic function on a compact surface →
  contradiction), *not* L²/Hodge-norm positivity; **discreteness** uses Abel + RR
  + the inverse function theorem. The trade is "combinatorial topology + PDE" →
  "compact operators + basic complex analysis," both well-developed in Mathlib.
- **C1: Partially correct — the one real caveat.** Forster reaches `H₁ ≅ ℤ^{2g}`
  only as an **abstract free abelian group** and builds `Jac(X)` strictly as a
  **complex torus**. He does **not** derive the symplectic basis, the intersection
  pairing, or the principal polarization. If/when we need the Jacobian to be an
  **algebraic (projective) abelian variety**, the intersection form / Riemann
  bilinear relations must be introduced then. Net: Route 1 buys the torus + lattice
  cheaply; the polarization is **deferred, not eliminated**.

Verdict: "Route 1 is vastly superior for Lean" for constructing the complex torus;
proceed, with the polarization tracked as explicitly deferred work.

## 4. Risks / open items

- **Dolbeault (§13)** is the one new analytic lemma to build (local ∂̄-solvability).
  Standard, local, but not yet in the project. Biggest single piece of new work.
- **`dim H¹(O)` vs `dim H⁰(Ω¹)`**: we hold the 1-form side; need to either run
  §16–17 from there or prove the structure-sheaf side. Bookkeeping, not depth.
- The two **mechanical bridge axioms** in `Bridge/KirovHolomorphic.lean` should
  be discharged so the keystone is fully axiom-clean.
- **Principal polarization is deferred, not free** (Gemini C1). Forster yields a
  complex torus; making `Jac(X)` a polarized abelian variety needs the
  intersection form + Riemann bilinear relations (`Im τ ≻ 0`) later. Decide
  whether the headline goal (challenge + Albanese) needs algebraicity — if it's
  torus-level, this can stay deferred; if it needs the projective/polarized
  structure, schedule `AX_RiemannBilinear` + intersection theory as a follow-on.
- Cross-check the whole chain against **Griffiths–Harris Ch. 0–2** (not yet in
  `refs/`) before committing, to confirm Forster's route has no hidden Hodge
  prerequisite we've missed.

## 5. Status

Proposal — for discussion before any code moves (touches the core axiom
interface; see CLAUDE.md "major changes"). The comparison and this plan are
recorded so the route decision is made with the prereq trees explicit rather
than by default-inheriting the GH/Hodge route the current `AX_*` plans assume.

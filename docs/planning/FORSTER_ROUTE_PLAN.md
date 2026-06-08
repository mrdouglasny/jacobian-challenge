# Forster-route discharge plan for the core period axioms

**Thesis.** Re-base the *period/torus* axiom discharges on Forster's cohomological
route (GTM 81, Ch. 2) instead of the Griffiths–Harris Hodge / period-matrix route
the current `AX_*` plans assume. Forster's route reaches `Jac(X)` as a complex
torus, and the full-rank period lattice, **without the 4g-gon topology or
polygon-Stokes** — the two biggest not-in-Mathlib line items of the current plans.

**Scope — three tiers (Codex review, §6).** Read this plan at three tiers, which
earlier drafts conflated:
- **Tier 1 — downstream reductions *assuming* RR/Serre as audited base axioms.**
  Sound and actionable now: use `AX_RiemannRoch`/`AX_SerreDuality` (+ Forster
  §19–21) to discharge the *period/torus* axioms (`AX_PeriodLattice`, the rank
  part of `AX_AnalyticCycleBasis`, …) and shrink dependency spread. The real
  near-term win; does **not** require proving RR/Serre.
- **Tier 2 — a faithful sheaf-cohomology layer.** Required before RR/Serre can be
  *claimed discharged*: must prove `SheafCohomologyFaithful`
  (`RiemannSurface/SheafCohomologySpec.lean`), which needs a **faithful `H1`**
  (currently an opaque placeholder — `LineBundle.lean:13`), not a stub.
- **Tier 3 — full RR/Serre discharge.** Heavy infrastructure: Čech `H¹(X, O_D)`
  for *all* divisors `D`, the long exact sequence, Dolbeault, residues/integration,
  Serre-pairing nondegeneracy.

The route's strength is **Tier 1**. Tiers 2–3 are a major infrastructure project;
earlier drafts understated this by calling the §14 keystone "banked" (it is not —
see §0).

Companion: [`JACOBIAN_ROUTE_COMPARISON.md`](JACOBIAN_ROUTE_COMPARISON.md) (the
route comparison + prereq trees).

---

## 0. What we actually have (and the keystone gap)

It is tempting to say the §14 finiteness keystone is already banked. **It is not**,
and the conflation is the substantive error Codex caught:

- **What we hold:** `FiniteDimensional ℂ (HolomorphicOneForm X)`, i.e.
  `dim H⁰(X, Ω¹) < ∞` — the *single* number, the 1-form side, via Kirov's Montel
  machinery (`Bridge/KirovHolomorphic.lean`; `AX_FiniteDimOneForms` retired
  2026-04-25, modulo two mechanical bridge axioms).
- **What §14 / Riemann–Roch needs:** `dim H¹(X, O_D) < ∞` for **every** divisor
  `D`, *and* a **faithful `H1`** functor with the Čech/long-exact-sequence
  machinery RR's inductive proof (Forster §16.7–16.10) runs on. Our `H1` is still
  an **opaque placeholder** (`LineBundle.lean:13`; `H0 = riemannRochSpace D` is
  de-opaqued, `H1` is not).
- **Why we can't bootstrap:** deriving `dim H¹(X, O) < ∞` from
  `dim H⁰(Ω¹) < ∞` goes *through Serre duality* — which is downstream, so the
  inference is **circular**. The structure-sheaf finiteness must be proved
  **directly** (the same Montel/compact-perturbation argument, applied to `O`/`O_D`,
  not the 1-forms). That is real new work, not banked.

So the Montel engine is genuinely reusable, but only as the *engine* for a
finiteness theorem we still have to state and prove on the structure sheaf —
**Tier 3**, not done.

The analytic-engine assets that *are* in place:
- `Jacobians/Vendor/Kirov/Montel/{Compactness,Complete,Cover,LocalRep,ChartNorm,
  SupNorm,ChartTransition}.lean` — the normal-families / Montel compactness layer.
- `riemannRochSpace D` — the real `L(D) = H⁰(O_D)` (de-opaqued, faithful).

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

## 1b. Tier 1 — the near-term win (start here)

This is the sound, immediately-actionable part, and it does **not** wait on the
Tier-2/3 sheaf-cohomology build. Treat `AX_RiemannRoch` and `AX_SerreDuality` as
**audited base axioms** (they already are — classified, cited Forster §16/§17),
and use them + Forster's §19–21 torus construction to **discharge the downstream
period/torus axioms**:
- `AX_PeriodLattice` (+ `instPeriodLatticeDiscrete`) — §21.4, from `dim Ω¹ = g`
  (a consequence of `AX_SerreDuality`, §17.10) + Abel + the maximum principle.
- the **rank** part of `AX_AnalyticCycleBasis` — `H₁ ≅ ℤ^{2g}` (§21.5), no 4g-gon.
- Abel-level consequences feeding `AX_AbelTheorem` and the period machinery.

Net effect: fewer *independent* deep axioms downstream, all funnelled through the
two audited RR/Serre axioms — without claiming RR/Serre themselves are proved.
This is the dependency-spread reduction Codex rates as the good path. **No major
infrastructure; can proceed as ordinary discharge PRs** (each still a "major
change" only insofar as it rewrites a core axiom — so: Discussion-linked, but no
new sheaf-cohomology layer required).

## 2. Build order (Tier 3 — the full RR/Serre discharge)

Steps 1–8 are the **Tier-3** infrastructure (do **not** start here for the
near-term win — see §1b for Tier-1). They are sequenced; each cites Forster + the
file it lands in.

1. **State + prove structure-sheaf finiteness directly.** `dim H¹(X, O_D) < ∞`
   for all `D`, via the Montel/compact-perturbation argument applied to `O`/`O_D`
   (Forster §14). **Do not** try to derive it from `dim H⁰(Ω¹) < ∞` — that routes
   through Serre and is circular (§0). Reuse the Kirov Montel layer as the engine,
   not the 1-form result as the conclusion. → `RiemannSurface/Cohomology/Finiteness.lean`.
2. **Čech `H¹(X,O)` + Dolbeault.** Forster §12–13. We have an `H1` type
   (`Cohomology/H1.lean`); need the structure-sheaf cohomology + the
   local-`∂̄`-solvability lemma (Dolbeault, §13). This is the main genuinely-new
   analytic lemma — but it is **strictly local/planar** (the `n=1`
   Grothendieck–Dolbeault lemma), so it needs no manifold topology. Standard proof
   = the **Cauchy–Pompeiu (generalized Cauchy integral) formula**: a local integral
   operator inverting `∂̄` on a disk. Mathlib's planar Cauchy theory
   (`Mathlib.Analysis.Complex.CauchyIntegral`, `Complex.integral`) is mature, so
   this reduces to multivariable real calculus + integral bounds — tedious but
   mechanical, no surface-Stokes. (Gemini-3 chat corroboration, 2026-06-07.)
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
- **`dim H¹(O)` vs `dim H⁰(Ω¹)` — a real gap, not bookkeeping** (Codex). We hold
  the 1-form side; RR needs structure-sheaf finiteness for all `O_D`. The two are
  linked only *by Serre*, so the structure-sheaf finiteness must be proved directly
  (§0, §2.1), not inherited. This is the Tier-3 entry cost.
- **Faithful `H1` gate (Tier 2).** RR/Serre cannot be *claimed discharged* until
  `SheafCohomologyFaithful` (`SheafCohomologySpec.lean`) is proved — i.e. `H1` is
  de-opaqued from its current placeholder to a faithful functor. This gate sits
  between Tier 1 (assume RR/Serre) and Tier 3 (prove them).
- The two **mechanical bridge axioms** in `Bridge/KirovHolomorphic.lean`
  (`bridgeForm` exists / injective) should be discharged **first** — both Gemini
  reviews flag this as the priority ("don't let `bridgeForm` remain an axiom for
  long … prevents foundational rot"). They're mechanically verifiable in Mathlib's
  bundle/section formalism and solidify the keystone the whole route stands on.
  This is also the lowest-risk concrete first step: it touches no core interface.
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

## 6. Codex review (2026-06-07) — "revise, not reject"

Codex rated the route a sound *strategic* direction but found the original draft
**overclaimed**, on two substantive points (not docs) and one cosmetic:

1. **Circular finiteness claim (substantive).** The draft said the §14 keystone
   was "already banked" because `HolomorphicOneForm X` is finite-dimensional. But
   that is `dim H⁰(Ω¹) < ∞`, *not* `dim H¹(X, O_D) < ∞`, not a faithful `H1`, and
   not the Čech/LES infrastructure RR/Serre run on. Linking the two needs Serre →
   circular. **Folded in:** §0 rewritten; §2.1 now mandates proving structure-sheaf
   finiteness directly.
2. **Missing sheaf-cohomology gate (substantive).** "Fully discharge RR/Serre"
   requires passing `SheafCohomologyFaithful` (`SheafCohomologySpec.lean`) — a
   faithful `H1`, currently an opaque placeholder. **Folded in:** the three-tier
   framing (Thesis, §1b, §4) makes Tier 2 explicit.
3. **Stale bridge-axiom note (docs only).** Acknowledged.

Codex's three-tier restructuring — now the spine of this doc:
- **Tier 1:** downstream reductions *assuming* RR/Serre (the good path, §1b).
- **Tier 2:** faithful sheaf-cohomology layer (`SheafCohomologyFaithful`).
- **Tier 3:** full RR/Serre discharge (H1 + LES + Dolbeault + residues + Serre
  pairing nondegeneracy).

Net of all three reviews (Gemini deep-think + Gemini-3 chat + Codex): the route is
**the right reorganization of the discharge strategy and the right way to retire
the period/torus axioms cheaply (Tier 1)** — but it is **not** a finished discharge
plan for RR/Serre themselves; Tiers 2–3 are a real infrastructure project whose
entry cost (direct structure-sheaf finiteness + a faithful `H1`) the first draft
understated.

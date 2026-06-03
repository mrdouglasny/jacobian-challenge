# `AX_SerreDuality` — discharge recipe

**Location:** `Jacobians/Axioms/SerreDuality.lean:54`
**Route:** needs-infra (reclassified from `mathlib-now [review]` per Gemini 3.1 Pro critique; not `genuine-textbook` either — the textbook proof rests on functional-analytic prerequisites that themselves require multi-month Mathlib infra builds) &nbsp;&nbsp; **Effort:** 10 &nbsp;&nbsp; **Est:** multi-quarter / multi-year; thousands of LOC across new Mathlib-adjacent infrastructure (Fréchet/Montel function spaces, integration of differential forms on manifolds, Čech cohomology of analytic sheaves). The "recipe itself, post-infra" framing in the previous draft was wrong — the infra *is* the work.
**Blocked by:** `LineBundle`, `H0`, `H1`, `Divisor`, `canonicalDivisor`, `PrincipalDivisors` (the entire sheaf-cohomology / line-bundle layer in `Jacobians/RiemannSurface/LineBundle.lean`), **plus** missing Mathlib infra: (i) integration of differential forms / Stokes on manifolds, (ii) Fréchet-space topology on spaces of holomorphic sections, (iii) Cartan–Serre finiteness (Schwartz's compact-perturbation lemma), (iv) Dolbeault complex on complex manifolds OR Čech cohomology with a usable Leray theorem for analytic sheaves. Paired infrastructurally with `AX_RiemannRoch` (`docs/planning/AX_RiemannRoch.md`) — both rest on the same sheaf-cohomology + analytic-topology layer; they must be planned together.

**Statement (verbatim):**
```lean
/-- **Axiom (Serre duality).** For a compact Riemann surface `X` and a
divisor `D`, there is a canonical ℂ-linear isomorphism

    H¹(X, 𝒪(D)) ≃ₗ[ℂ] Dual ℂ (H⁰(X, 𝒪(K − D))),

where `K := canonicalDivisor X` represents `Ω¹_X`. The isomorphism is
"perfect pairing" shape, packaged via `Nonempty` of the equivalence
to emphasize existence rather than a canonical choice. -/
axiom AX_SerreDuality {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) :
    Nonempty
      (H1 (LineBundle.ofDivisor D) ≃ₗ[ℂ]
        Module.Dual ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D))))
```

**Why it's an axiom right now:** Even the *signature* names `H0`, `H1`, `LineBundle.ofDivisor`, `canonicalDivisor`, all of which are themselves axiom stubs in `Jacobians/RiemannSurface/LineBundle.lean` (lines 85, 104, 128, 123 respectively). But the situation is much worse than just "axiom stubs need definitions". Serre duality on a compact complex manifold is one of the deepest theorems in complex geometry; its proof is *not* a routine algebraic exercise. The duality pairs a Fréchet space (Čech cochains with compact-open topology) with its topological dual, and only collapses to an algebraic isomorphism *because* finite-dimensionality (Cartan–Serre / Schwartz) is established first via functional analysis. Mathlib at this pin lacks: (a) integration of differential forms on manifolds; (b) the Dolbeault $\bar\partial$-complex and elliptic regularity for it; (c) Fréchet/Montel-space topology on $\mathcal{O}(U)$ for $U \subset X$ open; (d) Čech cohomology of sheaves on analytic spaces with Leray's theorem; (e) the Cartan B / Theorem B style vanishing on Stein open subsets needed to certify any concrete cover as Leray for the sheaf $\mathcal{O}(D)$.

**Gemini critique addressed:**
- *Route was wrong:* upgraded to `needs-infra`. The previous `genuine-textbook` (and original `mathlib-now [review]`) framings treated the prerequisites as cosmetic; in fact the prerequisites *are* multiple book-length Mathlib projects.
- *Effort was uncalibrated:* upgraded from 8 to 10. The "~150 LOC post-infra" claim is withdrawn — even with Čech cohomology in hand the non-degeneracy proof alone (Forster §17.4–17.10, which silently invokes Fréchet-space topology, closed-range theorem, and Hahn–Banach for locally convex spaces) is a substantial Lean undertaking on its own.
- *Hallucinated integration of forms:* Step 3 of the prior draft wrote `∫_X ∂̄η` as if this were a one-liner. It is not. Mathlib has no integration of differential forms on manifolds and no Stokes theorem for them; this is itself a multi-PR Mathlib gap and is now called out as a top-level blocker, not glossed over as "use a partition of unity".
- *Hallucinated functional analysis:* "Surjective by Hahn–Banach" and "$L^2$ density" were waved at as one-liners. They actually require the topological vector space structure on sheaf cohomology — Fréchet topology on $\check{C}^q(\mathcal{U}, \mathcal{O}(D))$, closed range of the Čech coboundary, Schwartz's compact-perturbation lemma. These are added as named prerequisites below, not buried in a half-sentence.
- *Hallucinated derived-functor shortcut:* the prior draft offered "use derived functors" as an alternative route. Mathlib's derived-category / homological-algebra API is not connected to complex analytic sheaves; this is *not* a shortcut and has been removed as a route.
- *Cartan–Serre finiteness was treated as a prerequisite to grab:* now explicitly listed as itself part of the missing infra, on the same footing as Serre duality.

**Proof recipe (route: build the analytic sheaf-cohomology + integration layer, then follow Forster Ch. II §17 / Griffiths–Harris Ch. 1 §2)**

This recipe assumes the **analytic / Hodge–Čech hybrid route**: build Dolbeault on $X$, integrate (1,1)-forms over $X$, and pair Čech cocycles against holomorphic 1-forms via the Dolbeault isomorphism and the integration pairing. References: **Forster, *Lectures on Riemann Surfaces*, Ch. II §17** (Čech presentation with full functional-analytic detail) and **Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2** ("Calculus on complex manifolds": Dolbeault, integration of $(p,q)$-forms, the trace map).

1. **Sheaf-cohomology layer for Riemann surfaces (infra prerequisite #1).** Promote the axiom stubs in `Jacobians/RiemannSurface/LineBundle.lean`: `Divisor` (`:51`), `Divisor.instAddCommGroup` (`:56`), `Divisor.deg` (`:63`), `PrincipalDivisors` (`:70`), `LineBundle` (`:77`), `H0` (`:85`), `H1` (`:104`), `canonicalDivisor` (`:123`), `LineBundle.ofDivisor` (`:128`) to real definitions. Concretely: `Divisor X := FreeAbelianGroup X`; $\mathcal{O}(D)$ as a locally-free analytic sheaf of rank 1; $H^0$, $H^1$ as Čech cohomology over a finite Stein cover. This is the keystone block listed in `ROADMAP.md` lines 121–125. **This step alone is multi-month** because it requires picking a sheaf API (presheaves on `Opens X` valued in `Module ℂ` is plausible; agreeing with future Mathlib analytic-sheaf API is delicate).

2. **Differential-form integration on manifolds (infra prerequisite #2).** Build (or wait for Mathlib to build) integration $\int_X \omega$ for compactly-supported smooth $(1,1)$-forms on a complex 1-manifold, plus Stokes' theorem for forms with corners. Without this, *every* statement involving the residue/integration pairing is uncheckable. Reference: Griffiths–Harris Ch. 1 §2 for the analytic content; the Lean infrastructure must rest on Mathlib's existing `MDifferentiable` / chart-by-chart Bochner integration machinery. **This is its own Mathlib-scale subproject.**

3. **Dolbeault complex for $\mathcal{O}(D)$ (infra prerequisite #3).** Define the smooth sections of $\mathcal{O}(D) \otimes \mathcal{A}^{p,q}$, the $\bar\partial$-operator, and the Dolbeault cohomology groups $H^{p,q}_{\bar\partial}(X, \mathcal{O}(D))$. Prove the Dolbeault isomorphism $H^q(X, \mathcal{O}(D)) \simeq H^{0,q}_{\bar\partial}(X, \mathcal{O}(D))$ — this requires the Poincaré $\bar\partial$-lemma on a disk (elliptic-regularity flavor; not currently in Mathlib in a usable form for analytic sheaves) plus a fine-resolution argument. Reference: Griffiths–Harris Ch. 1 §2, "The Dolbeault theorem". *Alternatively*: skip Dolbeault, do everything Čech-side following Forster §13–§17, and pay the cost in functional-analytic prerequisite #4.

4. **Functional-analytic topology on sections (infra prerequisite #4).** Equip $\mathcal{O}(D)(U)$ (and Čech cochain groups) with the Fréchet topology of uniform convergence on compacta. Prove: (a) Montel — bounded sets are relatively compact; (b) the Čech coboundary $\delta: \check{C}^0 \to \check{C}^1$ has closed range; (c) Cartan–Serre finiteness: $\dim_{\mathbb{C}} H^1(X, \mathcal{O}(D)) < \infty$, via Schwartz's compact-perturbation lemma. Reference: Forster §14 (Schwartz lemma) and §15 (finiteness). **This is the functional-analytic block that Gemini correctly flagged as completely missing from the prior draft.** It is independently book-scale.

5. **Construct the Serre pairing.** With infra (1)–(4) in hand: given $\xi \in H^1(X, \mathcal{O}(D))$ (Dolbeault representative $\xi \in \mathcal{A}^{0,1}(X, \mathcal{O}(D))$, $\bar\partial$-closed) and $\omega \in H^0(X, \Omega^1(-D))$, the wedge $\omega \wedge \xi$ is a smooth $(1,1)$-form on $X$. Define $\langle \xi, \omega \rangle := \frac{1}{2\pi i} \int_X \omega \wedge \xi$. Show well-definedness on cohomology classes using Stokes. (Forster §17.4 does this on the Čech side using a partition of unity and is harder to formalize without infra (4).) Reference: Griffiths–Harris Ch. 1 §2, integration / trace map.

6. **Non-degeneracy + packaging.** Prove the induced map $H^1(X, \mathcal{O}(D)) \to \mathrm{Hom}_{\mathbb{C}}(H^0(X, \Omega^1(-D)), \mathbb{C})$ is bijective: injectivity from Hahn–Banach for Fréchet spaces (uses closed-range from (4)); surjectivity from finite-dimensionality of $H^0$ (Cartan–Serre, again from (4)). Reference: Forster §17.5–§17.10. Then wrap the resulting $\mathbb{C}$-linear iso with `Nonempty` per the statement's existential framing. Finally, in `Jacobians/Axioms/SerreDuality.lean:54`, replace `axiom AX_SerreDuality ...` with `theorem AX_SerreDuality ... := ⟨serreDualityEquiv D⟩`.

**Next discrete deliverable.** *Not* a Lean step — escalate. Before any Lean code is written, write a 1-page coordination memo for the human triaging `AX_RiemannRoch` and `AX_SerreDuality` jointly: which of infra (1)–(4) is realistic to attempt in this repo vs. should wait for Mathlib upstream, and whether the project should keep both as axioms in the medium term (and instead invest the discharge budget elsewhere). The cheapest possible Lean step that is *not* premature is promoting `Divisor` and `Divisor.deg` (`Jacobians/RiemannSurface/LineBundle.lean:51, :63`) to real definitions via `FreeAbelianGroup X` and `FreeAbelianGroup.sum` — but this is a typechecking-experiment-only deliverable; it makes no progress on the duality theorem itself.

**Files touched**
- `Jacobians/RiemannSurface/LineBundle.lean` — replace `Divisor` (`:51`), `Divisor.instAddCommGroup` (`:56`), `Divisor.deg` (`:63`), `PrincipalDivisors` (`:70`), `LineBundle` (`:77`), `H0` (`:85`), `H0.instAddCommGroup` (`:90`), `H0.instModule` (`:96`), `H1` (`:104`), `H1.instAddCommGroup` (`:108`), `H1.instModule` (`:114`), `canonicalDivisor` (`:123`), `LineBundle.ofDivisor` (`:128`) axiom stubs with real definitions.
- `Jacobians/Axioms/SerreDuality.lean` — replace `axiom AX_SerreDuality` (line 54) with `theorem AX_SerreDuality` whose body is `⟨serreDualityEquiv D⟩`.
- (new) `Jacobians/RiemannSurface/CechCohomology.lean` — Čech cohomology of analytic sheaves on a finite Leray cover, including topology of cochains.
- (new) `Jacobians/RiemannSurface/Dolbeault.lean` — Dolbeault complex on a complex 1-manifold and the Dolbeault isomorphism for $\mathcal{O}(D)$.
- (new) `Jacobians/RiemannSurface/SectionsTopology.lean` — Fréchet/Montel topology on $\mathcal{O}(D)(U)$, closed-range of $\delta$, Schwartz / Cartan–Serre finiteness.
- (new) `Jacobians/Analysis/FormIntegration.lean` — integration of compactly-supported $(p,q)$-forms on a complex manifold (or imported from Mathlib once upstreamed).
- (new) `Jacobians/RiemannSurface/SerrePairing.lean` — the integration pairing of Step 5 and its non-degeneracy lemma (Step 6).
- `Jacobians/Axioms/RiemannRoch.lean` — no signature change, but coordination with this file is required since both axioms share infra (see paired plan).

**Acceptance**
- All of infra prerequisites (1)–(4) compile; each has its own acceptance gate (axiom-count delta logged per sub-PR).
- `lake build Jacobians.Axioms.SerreDuality` succeeds with the axiom replaced by a theorem (no `sorry`).
- `#print axioms AX_genus_eq_zero_iff_homeo` no longer lists `AX_SerreDuality`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by ≥ 1 (substantially more if the whole sheaf-cohomology + analytic-topology layer lands in the same campaign).

**Risk / escalation triggers**
- **Default state is escalate.** Before any of infra (1)–(4) is started, escalate to a human to confirm the project actually wants to absorb a multi-quarter analytic-infra investment in-tree rather than wait for Mathlib's `Mathlib.Geometry.RingedSpace` / `Mathlib.AlgebraicGeometry.Sheaves` or upstream analytic-sheaf API. If Mathlib lands either coherent-sheaf cohomology on analytic spaces or a usable Dolbeault complex, immediately reroute and discard most of (3)/(4).
- If a sub-PR for Cartan–Serre finiteness (infra 4) requires Schwartz's compact-perturbation lemma and that is not in Mathlib, escalate — that is itself a textbook-scale sub-project.
- If the Dolbeault $\bar\partial$-Poincaré lemma on a disk turns out to need general elliptic regularity machinery beyond what Mathlib has, escalate — coordinate with `AX_RiemannBilinear` (`docs/planning/AX_RiemannBilinear.md`), which hits the same blocker.

---
**Vetting trail.** Critique: `_vetting/AX_SerreDuality.md`. Verdict: reject. Revised: 2026-06-03.

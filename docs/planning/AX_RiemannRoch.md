# `AX_RiemannRoch` — discharge recipe

**Location:** `Jacobians/Axioms/RiemannRoch.lean:59`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 10 &nbsp;&nbsp; **Est:** the Euler-characteristic induction proper is ~1–2 focused months and ~600–1000 LOC *once the two `needs-infra` prerequisites below have landed*; the prerequisite infra (sheaf-cohomology LES + Serre Finiteness) is a multi-year ~15K+ LOC undertaking tracked under separate plans
**Blocked by:** `AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54`); plus two `needs-infra` plans listed under "Sub-plans needed" below (Čech LES via Leray; Serre Finiteness for compact Riemann surfaces). Also still consumes the `LineBundle.lean` axiom stubs as concrete defs — `Divisor` (`Jacobians/RiemannSurface/LineBundle.lean:51`), `Divisor.deg` (line 63), `LineBundle.ofDivisor` (line 128), `H0` (line 85), `H1` (line 104).

**Statement (verbatim):**
```lean
/-- **Axiom (Riemann-Roch).** For a compact Riemann surface `X` and a
divisor `D` on `X` (with `H⁰(O(D))` and `H¹(O(D))` both
finite-dimensional, which holds classically by compactness):

    dim H⁰(X, 𝒪(D)) − dim H¹(X, 𝒪(D)) = deg D + 1 − g.

Both sides cast to `ℤ` to avoid `Nat`-subtraction truncation. -/
axiom AX_RiemannRoch {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (D : Divisor X)
    [_h0fd : FiniteDimensional ℂ (H0 (LineBundle.ofDivisor D))]
    [_h1fd : FiniteDimensional ℂ (H1 (LineBundle.ofDivisor D))] :
    (Module.finrank ℂ (H0 (LineBundle.ofDivisor D)) : ℤ) -
    (Module.finrank ℂ (H1 (LineBundle.ofDivisor D)) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ)
```

**Why it's an axiom right now:** Riemann–Roch is the keystone theorem of the project but Mathlib (at the project's pin) has neither sheaf cohomology of locally-free sheaves on complex manifolds nor the analytic machinery (Serre finiteness via Fréchet/Montel spaces, Schwartz's theorem on compact perturbations) needed to prove the prerequisites. The objects on its left-hand side (`H0`, `H1`, `LineBundle.ofDivisor`, `Divisor.deg`) are themselves opaque axiom-level stubs (`Jacobians/RiemannSurface/LineBundle.lean:51–130`) and `genus X` is `Module.finrank ℂ (HolomorphicOneForm X)` (`Jacobians/RiemannSurface/Genus.lean:39`). This recipe was previously misclassified `genuine-textbook`; per Gemini 3.1 Pro critique (2026-06-03) it is reclassified `provable-from-other-axioms` because the proof reduces RR to `AX_SerreDuality` plus two `needs-infra` sub-plans (see below).

**Scope of THIS recipe.** *Only* the Euler-characteristic induction. We take as given:

- **(P1)** Serre Finiteness for compact Riemann surfaces — i.e. for any holomorphic line bundle `L` on a compact `X`, `H0 L` and `H1 L` are finite-dimensional over `ℂ`. Provided by the sub-plan `AX_RiemannRoch_SerreFiniteness` (see below). Until that lands, this recipe keeps the `[_h0fd]` / `[_h1fd]` typeclass hypotheses in the axiom signature exactly as written.
- **(P2)** Čech-cohomology long exact sequence — i.e. a short exact sequence of `𝒪_X`-modules `0 → 𝒜 → ℬ → 𝒞 → 0` yields a six-term LES `0 → H⁰𝒜 → H⁰ℬ → H⁰𝒞 → H¹𝒜 → H¹ℬ → H¹𝒞 → 0` (on a 1-real-dimensional-base, so `H²` vanishes). **Logical-gap note (from critique):** for Čech cohomology this is *not* automatic from naive cocycle definitions; one must either pass to the direct limit over covers with paracompactness, or formalise Leray's theorem so that Čech agrees with derived-functor cohomology. Provided by the sub-plan `AX_RiemannRoch_CechLES` (see below).
- **(P3)** `AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54`) — gives `H¹(X, 𝒪_X) ≃ H⁰(X, Ω¹)*` and hence `finrank ℂ (H1 𝒪) = genus X`. This is what reclassifies the route as `provable-from-other-axioms`.

**Proof recipe** (the induction; assumes P1, P2, P3)

1. **Establish the point-residue short exact sequence.** For any `P ∈ X` and any divisor `D`, the inclusion of `𝒪_X`-modules `𝒪(D) ↪ 𝒪(D + P)` has cokernel the skyscraper sheaf `ℂ_P` (Forster §16.5; Miranda VI.3): a section of `𝒪(D + P)` near `P` is determined modulo `𝒪(D)` by its residue at `P`. Formalised as `0 → LineBundle.ofDivisor D → LineBundle.ofDivisor (D + ⟨P⟩) → SkyscraperSheaf ℂ P → 0`. Bookkeeping only — no analysis.

2. **Apply the LES (P2) to get the six-term exact sequence.**
   `0 → H0 𝒪(D) → H0 𝒪(D+P) → H0 ℂ_P → H1 𝒪(D) → H1 𝒪(D+P) → H1 ℂ_P → 0`.
   We have `H0 ℂ_P ≃ ℂ` (global sections of a skyscraper) and `H1 ℂ_P = 0` (skyscraper has no higher cohomology on any reasonable site). With (P1), every term is finite-dimensional, so alternating-sum / rank-nullity on the exact sequence yields
   `χ(D + P) − χ(D) = finrank H0 ℂ_P − finrank H1 ℂ_P = 1`,
   where `χ(D) := (finrank ℂ (H0 (LineBundle.ofDivisor D)) : ℤ) − (finrank ℂ (H1 (LineBundle.ofDivisor D)) : ℤ)`.

3. **Euler-characteristic induction.** From step 2 and the dual exact sequence (subtract a point instead of add one), `χ(D ± P) = χ(D) ± 1`, hence `χ(D) − Divisor.deg X D` is invariant under adding or removing single points. Since `Divisor X` is by construction `FreeAbelianGroup X` (sub-plan landing the real `Divisor` def replaces the axiom at `LineBundle.lean:51`), every divisor is reachable from `0` by finitely many point-additions/-subtractions. Hence `χ(D) − Divisor.deg X D = χ(0)` for every `D`. Formalise as `RiemannRoch.chi_sub_deg_eq` in a new file (see below).

4. **Compute the base case `χ(0)` using `AX_SerreDuality` (P3).**
   - `H0 (LineBundle.ofDivisor 0) = H⁰(X, 𝒪_X) ≃ ℂ` (constants on a connected compact Riemann surface — uses `[ConnectedSpace X] [CompactSpace X]`; this is the maximum-modulus principle applied to holomorphic functions, which our existing analytic-manifold layer supplies). Hence `finrank ℂ (H0 (LineBundle.ofDivisor 0)) = 1`.
   - By `AX_SerreDuality` instantiated at the structure sheaf: `H1 (LineBundle.ofDivisor 0) ≃ (H0 Ω¹_X)*`, where `Ω¹_X = LineBundle.ofDivisor (canonicalDivisor X)`. The dual of an `n`-dim space is `n`-dim, and `H0 Ω¹_X = HolomorphicOneForm X` by definition (this is the bridge lemma `genus_eq_finrank_H1_structureSheaf` flagged in the original plan). Hence `finrank ℂ (H1 (LineBundle.ofDivisor 0)) = genus X` by `Genus.lean:39`.
   - Therefore `χ(0) = 1 − (genus X : ℤ)`.

5. **Conclude.** Combining steps 3 + 4: `χ(D) = Divisor.deg X D + 1 − (genus X : ℤ)`, which is exactly the LHS=RHS of the axiom. Replace `axiom AX_RiemannRoch` with `theorem AX_RiemannRoch` in `Jacobians/Axioms/RiemannRoch.lean:59`. Keep the `[_h0fd]` / `[_h1fd]` hypotheses for now; they can only be dropped once (P1) lands as a real instance.

**Next discrete deliverable.** Step 1 — formalise the point-residue SES `0 → 𝒪(D) → 𝒪(D + P) → ℂ_P → 0` as a stand-alone lemma in a new file `Jacobians/RiemannSurface/RiemannRoch/PointResidueSES.lean`. This is the smallest piece that exercises the `LineBundle.ofDivisor` API and is unblocked the moment `Divisor` and `Divisor.deg` (the two `mathlib-now` stubs at `LineBundle.lean:51,63`) are landed as real definitions over `FreeAbelianGroup X`.

**Files touched**
- `Jacobians/Axioms/RiemannRoch.lean` — replace `axiom AX_RiemannRoch` (line 59) with `theorem AX_RiemannRoch`. Keep `[_h0fd]` / `[_h1fd]` typeclass hypotheses (drop only after the Serre-Finiteness sub-plan lands).
- `Jacobians/RiemannSurface/Genus.lean` — add bridge lemma `genus_eq_finrank_H1_structureSheaf : genus X = Module.finrank ℂ (H1 (LineBundle.ofDivisor 0))` (uses `AX_SerreDuality`).
- New file `Jacobians/RiemannSurface/RiemannRoch/PointResidueSES.lean` — the point-residue SES of step 1.
- New file `Jacobians/RiemannSurface/RiemannRoch/Induction.lean` — `chi_sub_deg_eq` (step 3) and the base case (step 4).
- *(Out of scope for this recipe — see "Sub-plans needed":)* `Jacobians/RiemannSurface/SheafCohomology/CechLES.lean`, `Jacobians/RiemannSurface/SheafCohomology/SerreFiniteness.lean`.

**Acceptance**
- `lake build Jacobians.Axioms.RiemannRoch` succeeds with `AX_RiemannRoch` as a `theorem`, not an `axiom` (modulo the still-axiomatic `AX_SerreDuality` and the two infra stubs from the sub-plans).
- `#print axioms AX_RiemannRoch` no longer self-references; it does list `AX_SerreDuality` and the two infra axioms from the sub-plans (this is expected for a `provable-from-other-axioms` discharge).
- `#print axioms AX_genus_eq_zero_iff_homeo` (`Jacobians/Axioms/Uniformization0.lean:55`) no longer lists `AX_RiemannRoch` directly.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (RR itself); the infra axioms are tracked by their own plans.

**Risk / escalation triggers**
- Either sub-plan below cannot be cleanly stated as a `needs-infra` bounded API (e.g. Leray's theorem turns out to require a deeper paracompactness layer Mathlib lacks) — stop and re-classify under ROADMAP.
- The base-case computation `H⁰(X, 𝒪_X) ≃ ℂ` (step 4) turns out *not* to follow from our existing analytic-manifold layer (i.e. we lack a usable max-modulus principle for global holomorphic functions on compact connected `X`) — stop and add it as a separate `mathlib-now`/`provable` plan before continuing.
- The statement signature changes (e.g. dropping `[_h0fd]` / `[_h1fd]` forces a different `H0` / `H1` shape) — stop and re-classify in ROADMAP.

**Gemini critique addressed:**
- **Route reclassified** from `genuine-textbook` to `provable-from-other-axioms`: the proof explicitly reduces to `AX_SerreDuality` for the base case, so the previous label was wrong.
- **Logical Čech-LES gap flagged**: the original Step 3 silently assumed a Čech long exact sequence, which is not exact without passing to direct limits over covers or invoking Leray's theorem. We now take the LES as an explicit assumed prerequisite (P2) and split it off into its own `needs-infra` sub-plan that names Leray's theorem.
- **Scope honestly split**: the monolithic 2–4K-LOC estimate was naive (real number is 15K+ LOC dominated by Fréchet/Montel functional analysis for Serre Finiteness). This recipe now covers *only* the Euler-characteristic induction (bounded: ~600–1000 LOC); the brutal infra is tracked under two named sub-plans below.

## Sub-plans needed

The project should add two new `needs-infra` plans alongside this one. They are listed here so the critical path is visible.

1. **`AX_RiemannRoch_CechLES.md`** (`needs-infra`, est ~5K–8K LOC). Build a Čech-cohomology API for `𝒪_X`-modules on a (paracompact, Hausdorff) topological space and prove that a short exact sequence of sheaves yields a six-term long exact sequence in cohomology. Key sub-deliverables: (i) Čech complex over an open cover; (ii) refinement maps and the colimit `Ȟ^i(X, ℱ) := colim_𝒰 Ȟ^i(𝒰, ℱ)`; (iii) exactness of the colimit on paracompact spaces (Godement-style); (iv) **Leray's theorem** — for a cover by acyclic opens, Čech cohomology of the cover equals derived-functor / colimit cohomology. (iv) is the lynchpin that makes the LES exact for Stein-like covers on Riemann surfaces. Without this, Step 2 of THIS recipe is mathematically unjustified.

2. **`AX_RiemannRoch_SerreFiniteness.md`** (`needs-infra`, est ~7K–10K LOC). Prove Forster Ch. 14: for any holomorphic line bundle `L` on a compact Riemann surface `X`, both `H0 L` and `H1 L` are finite-dimensional over `ℂ`. This is the analytic-functional-analysis core: Fréchet space structure on sections, Montel's theorem, the open mapping theorem for Fréchet spaces, and **Schwartz's theorem on compact perturbations of the identity** (the cornerstone of the proof). When this lands, the `[_h0fd]` and `[_h1fd]` typeclass hypotheses in `AX_RiemannRoch` (and the dozens of downstream lemmas that drag them along) can be dropped wholesale.

---
**Vetting trail.** Critique: `_vetting/AX_RiemannRoch.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.

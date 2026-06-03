# `H0.instModule` — discharge recipe

**Location:** `Jacobians/RiemannSurface/LineBundle.lean:96`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~15 minutes, ~3 LOC (effectively 0 effort, bundled in the same PR as `H0`)
**Blocked by:** `H0` (`Jacobians/RiemannSurface/LineBundle.lean:85`), `H0.instAddCommGroup` (`:90`)

**Statement (verbatim):**
```lean
axiom H0.instModule {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    Module ℂ (H0 L)
attribute [instance] H0.instModule
```

**Why it's an axiom right now:** Companion to `H0.instAddCommGroup`. Global sections of an analytic line bundle `L = 𝒪(D)` carry a canonical ℂ-module structure. The instance is `axiom` only because its carrier `H0 L` is `axiom`-opaque. Once `H0` becomes a real `def` evaluating the sheaf at the global section `⊤`, the `Module ℂ` instance propagates automatically.

**Proof recipe**

1. Per the `LineBundle` discharge, `LineBundle D` is the lightweight `PUnit` token and carries no sheaf data. The sheaf of sections used here must therefore be the `Sheaf (ModuleCat ℂ) X` constructed locally from the divisor `D` argument (already in scope as `{D : Divisor X}`), e.g. via `sheafOfDivisor D`. Sheaf data must NOT be projected off `L`.
2. When defining `H0 L`, do *not* use derived functors, `Ext` groups, or `Sheaf.H 0` machinery. Define it simply as the evaluation of the divisor-derived sheaf on the whole space: `(sheafOfDivisor D).val.obj (op ⊤)`. Because the sheaf is valued in `ModuleCat ℂ`, the `Module ℂ` instance on global sections is definitionally free.
3. Replace the axiom with an `instance` whose body is `inferInstance`. In `Jacobians/RiemannSurface/LineBundle.lean:96`, change:
   ```lean
   axiom H0.instModule {X : Type*} [...] (L : LineBundle D) :
       Module ℂ (H0 L)
   attribute [instance] H0.instModule
   ```
   to:
   ```lean
   instance H0.instModule {X : Type*} [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ, ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
       Module ℂ (H0 L) := inferInstance
   ```
   Delete the redundant `attribute [instance]` line at `:100`.
4. Bundle this change in the exact same PR that defines `H0` and `H0.instAddCommGroup`. They must not be discharged in separate files or PRs.

**Files touched**
- `Jacobians/RiemannSurface/LineBundle.lean` — replace `axiom H0.instModule` (line 96) with `instance H0.instModule ... := inferInstance`; drop the now-redundant `attribute [instance]` declaration at line 100.

**Acceptance**
- `lake build Jacobians.RiemannSurface.LineBundle` succeeds.
- `#print axioms AX_RiemannRoch` (`Jacobians/Axioms/RiemannRoch.lean:59`) no longer lists `H0.instModule`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Escalate immediately if `LineBundle` is constructed such that it only exposes an `AddCommGroup` (e.g., valued in `AddCommGroupCat`) rather than `ModuleCat ℂ`. This means the foundational complex geometry setup is wrong and must be corrected before proceeding.

**Gemini critique addressed:**
- Eliminated the `Ext`/`Sheaf.H 0` conceptual overkill; explicitly mandated that `H0` simply evaluate `F.val.obj (op ⊤)`.
- Upgraded the `LineBundle` output category from a "risk" to a strict, non-negotiable requirement: it must be a sheaf valued in `ModuleCat ℂ`.
- Specified that `H0.instModule` must be discharged in the exact same PR as the `H0` definition rather than treated as an isolated task.

---
**Vetting trail.** Critique: `_vetting/H0-instModule.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Refactored to not project `.sheaf` off the `PUnit`-token `LineBundle`; sheaf data is now built from the divisor `D` argument directly.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.

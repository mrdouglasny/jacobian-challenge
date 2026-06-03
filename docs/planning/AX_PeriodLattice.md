# `AX_PeriodLattice` — discharge recipe

**Location:** `Jacobians/Axioms/PeriodLattice.lean:92`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 4 &nbsp;&nbsp; **Est:** ~3–5 focused days, ~150–250 LOC (shares ~70% of its derivation with `instPeriodLatticeDiscrete`)
**Blocked by:** `AX_RiemannBilinear`

**Statement (verbatim):**
```lean
/-- **Axiom (NOT VERIFIED).** In basis coordinates, the image of the period
map is a full `ℤ`-lattice in `Fin (genus X) → ℂ`.

Mathematical source: the classical period-lattice theorem, equivalently the
combination of Riemann's bilinear relations with the rank computation
`rank H₁(X, ℤ) = 2g`. This is the exact hypothesis needed to feed the
period image into `AbelianVariety.ComplexTorus`. -/
axiom AX_PeriodLattice (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    IsZLattice ℝ (periodLatticeInBasis X x₀ b)
```

**Why it's an axiom right now:** The file's docstring (lines 25–34, 85–91) records the discharge route: classical period-lattice theorem (Mumford II.2; Griffiths–Harris Ch. 2 §2) = Riemann bilinear relations + `rank H₁(X, ℤ) = 2g`. The class `IsZLattice ℝ L` (`Mathlib.Algebra.Module.ZLattice.Basic:435–438`) requires `span ℝ (L : Set E) = ⊤`. The blocker is `AX_RiemannBilinear` (`Jacobians/Axioms/RiemannBilinear.lean:69`), which produces the symmetric `τ : SiegelUpperHalfSpace (genus X)` whose positive-definite `Im τ` forces the `2g` period vectors to be ℝ-linearly independent; `rank H₁(X, ℤ) = 2g` is no longer an axiom (now `theorem AX_H1FreeRank2g` at `Jacobians/Axioms/H1FreeRank2g.lean:41`, derived from `AX_AnalyticCycleBasis`). Consumers: `Jacobian/Construction.lean:135–136` and all `*_preserves_lattice` axioms in `Jacobians/Axioms/AbelJacobiMap.lean` (lines 316–460).

**Proof recipe**

Mumford, *Tata Lectures on Theta I*, Ch. II §2, Thm II.2.1; Forster, *Lectures on Riemann Surfaces*, Ch. IV §20–21; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 2 §2. The plan reuses steps 1–5 of `instPeriodLatticeDiscrete.md` to build a concrete ℝ-basis of the ambient space whose ℤ-span equals the period lattice, then concludes via Mathlib's `instIsZLatticeRealSpan`.

1. **Obtain the symplectic data from `AX_RiemannBilinear`.** Cite
   `Jacobians/Axioms/RiemannBilinear.lean:69`. Destruct to get
   `⟨b₀, cω, τ, hA, hτ⟩`, with `b₀ : AnalyticCycleBasis X x₀`
   (basis at `b₀.isBasis`, `Jacobians/Axioms/AnalyticCycleBasis.lean:230`),
   `cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)` α-normalized,
   and `τ : SiegelUpperHalfSpace (genus X)` (symmetric, `Im τ` positive
   definite via `Jacobians/AbelianVariety/Siegel.lean:51, 54`).

2. **Evaluate `periodMapInBasis X x₀ cω` on the symplectic basis.** Using
   `periodMapInBasis` (`Jacobians/Axioms/PeriodLattice.lean:53–58`) and
   `αEmbed` / `βEmbed` (`AnalyticCycleBasis.lean:198, 205`), the α-block of
   the period map sends `b₀.isBasis (αEmbed i)` to `Pi.single i 1` (`e_i`),
   and the β-block sends `b₀.isBasis (βEmbed i)` to the `i`-th row of `τ.val`
   (a vector in `Fin (genus X) → ℂ`). Same computation as step 2 of
   `instPeriodLatticeDiscrete.md`.

3. **Assemble the candidate ℝ-basis `v` of `Fin (genus X) → ℂ`.** Define
   ```
   v : Fin (2 * genus X) → (Fin (genus X) → ℂ)
   v (αEmbed i) := Pi.single i 1                   -- e_i
   v (βEmbed i) := fun j => τ.val i j              -- i-th row of τ
   ```
   (the `αEmbed`/`βEmbed` Sum.elim covers `Fin (2 * genus X)` by
   `AnalyticCycleBasis.lean:198–208`).

4. **ℝ-linear independence of `v` from `Im τ` positive definite.** Suppose
   `Σ_i a_i · e_i + Σ_i c_i · τᵢ = 0` over ℝ with `a, c : Fin (genus X) → ℝ`.
   Taking the imaginary part component-wise and using `τ.val i j ∈ ℂ`: the
   real part gives `a_j + Σ_i c_i · Re(τ i j) = 0` (forces `a` once `c` is
   known); the imaginary part gives `Σ_i c_i · Im(τ i j) = 0`, i.e.
   `c · (Im τ) = 0` as a row vector. Because `τ.imPosDef`
   (`Jacobians/AbelianVariety/Siegel.lean:54`) provides `PosDef` on
   `τ.val.map Complex.im`, this forces `c = 0`, then `a = 0`. Conclude
   `LinearIndependent ℝ v`.

5. **Card = ℝ-dim.** `Module.finrank ℝ (Fin (genus X) → ℂ) = 2 * genus X` via
   `Complex.finrank_real_complex` (used identically at
   `Jacobians/ProjectiveCurve/Elliptic.lean:62–63`) plus
   `Module.finrank_pi`. So `Fintype.card (Fin (2 * genus X)) = finrank ℝ _`.
   Package `v` into `vBasis : Module.Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ)`
   via `basisOfLinearIndependentOfCardEqFinrank` (the same Mathlib helper
   instantiated at `Jacobians/ProjectiveCurve/Elliptic.lean:62`).

6. **Identify `periodLatticeInBasis X x₀ cω` with `Submodule.span ℤ (Set.range vBasis)`.**
   By step 2, the generators of `LinearMap.range (periodMapInBasis X x₀ cω)`
   (the definition of `periodLatticeInBasis` at
   `Jacobians/Axioms/PeriodLattice.lean:63–68`) over the ℤ-basis `b₀.isBasis`
   are exactly the values of `v`. Both sides are `Submodule ℤ` of
   `Fin (genus X) → ℂ`, finitely generated by the same `2g` vectors, so they
   coincide: `periodLatticeInBasis X x₀ cω = Submodule.span ℤ (Set.range vBasis)`.

7. **Apply `instIsZLatticeRealSpan`.** Mathlib's instance
   (`Mathlib.Algebra.Module.ZLattice.Basic:440–443`)
   ```
   instance instIsZLatticeRealSpan {E ι : Type*} [NormedAddCommGroup E]
       [NormedSpace ℝ E] [Finite ι] (b : Basis ι ℝ E) :
       IsZLattice ℝ (span ℤ (Set.range b)) where span_top := ZSpan.span_top b
   ```
   fires with `E := Fin (genus X) → ℂ`, `ι := Fin (2 * genus X)`,
   `b := vBasis`. Conclude `IsZLattice ℝ (periodLatticeInBasis X x₀ cω)`.

8. **Transport along basis change `cω ↔ b`.** The given basis `b` differs
   from `cω` by `M : Matrix (Fin (genus X)) (Fin (genus X)) ℂ` (invertible).
   The change-of-basis on `periodMapInBasis` is
   `periodMapInBasis X x₀ b = M.toLin' ∘ₗ periodMapInBasis X x₀ cω`
   (read off the definition, lines 57–58). So
   `periodLatticeInBasis X x₀ b = Submodule.map M.toLin' (periodLatticeInBasis X x₀ cω)`.
   Mathlib's `instIsZLatticeComap` (`ZLattice/Basic.lean:723–728`) gives
   `IsZLattice K` transport along a `ContinuousLinearEquiv`; cast
   `M.toLin'` as a continuous ℝ-linear equiv (continuity is free in
   finite-dim) and conclude `IsZLattice ℝ (periodLatticeInBasis X x₀ b)`.

9. **Replace `axiom AX_PeriodLattice` with `theorem` (or `instance`) in
   `Jacobians/Axioms/PeriodLattice.lean:92`** and keep
   `attribute [instance]` on line 98 so downstream
   (`Jacobian/Construction.lean:135–136`,
   `Vendor/Kirov/ZLatticeQuotient.lean:84, 144, 642, 741`) keeps finding it.

**Shared helpers note.** Steps 1–6 are identical to steps 1–5 of
`instPeriodLatticeDiscrete.md`. Land them once in
`Jacobians/RiemannSurface/PeriodBasis.lean` (new) and have *both* axiom
files cite the shared lemma `periodLatticeInBasis_eq_span_v` (step 6).
`instPeriodLatticeDiscrete` then needs only the discreteness corollary
(`ZLattice/Basic.lean:320`); `AX_PeriodLattice` needs only step 7
(`instIsZLatticeRealSpan` at `ZLattice/Basic.lean:440`).

**Files touched**
- `Jacobians/Axioms/PeriodLattice.lean` — replace `axiom AX_PeriodLattice`
  (line 92) with `theorem` / `instance`; preserve `attribute [instance]` on
  line 98.
- `Jacobians/RiemannSurface/PeriodBasis.lean` *(new, shared with
  `instPeriodLatticeDiscrete`)* — defines the ℝ-basis `vBasis` (steps 3–5),
  proves the ℤ-span identification (step 6), and the basis-change transport
  (step 8).

**Acceptance**
- `lake build Jacobians.Axioms.PeriodLattice` succeeds.
- `#print axioms Jacobians.Jacobian.Construction.JacobianAmbient` (at
  `Jacobians/Jacobian/Construction.lean:132–136`, the immediate consumer) no
  longer lists `AX_PeriodLattice`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS;
  axiom count drops by 1 (drops by 2 once `instPeriodLatticeDiscrete` lands
  alongside, since both share the same supporting lemma file).

**Risk / escalation triggers**
- If the `Im τ` positive-definiteness extracted from
  `Jacobians/AbelianVariety/Siegel.lean:54` (entry-wise `Matrix.PosDef`) is
  in a form incompatible with the ℝ-linear-independence argument of step 4
  (e.g. row-vs-column convention, or `PosDef` on `(τ.map Complex.im)`
  rather than on `τ.val.map Complex.im` due to a `map`-application
  mismatch), escalate — may require an additional adapter lemma in
  `Siegel.lean`.
- If Mathlib's `instIsZLatticeComap` (step 8) is unavailable for the
  basis-change transport because `M.toLin'` cannot be packaged as a
  `ContinuousLinearEquiv` in the chosen norm setup, escalate — fallback is
  to redo steps 3–6 directly with the basis `b` instead of `cω`, but that
  loses the shared-helper structure with `instPeriodLatticeDiscrete`.
- If `periodMapInBasis X x₀ cω` evaluated on `b₀.isBasis (αEmbed i)` fails
  to reduce to `Pi.single i 1` because `b₀.isBasis` is only `Module.Basis`
  over ℤ (not ℂ) and the `equivFun.toLinearMap.restrictScalars ℤ` step
  (`PeriodLattice.lean:58`) does not commute with the dual-basis evaluation
  as expected, escalate — the `periodMapInBasis` definition itself may need
  a reformulation before either axiom can be discharged.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.

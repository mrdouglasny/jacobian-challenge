# Gemini 3 Pro review — Part A definitions (Theta, Siegel, ComplexTorus)

Date: 2026-04-21.
Reviewer: `gemini-3-pro-preview` via `chat_gemini` (Deep Think still 500-ing).
Scope: vet Theta.lean, Siegel.lean, ComplexTorus.lean for math correctness, Lean 4 idiomaticity, and looming architectural issues.

---

## Math correctness (Theta)

All three math-correctness questions cleared:

1. `dotProduct nC (τ.val *ᵥ nC)` **is** the Mathlib idiom for `nᵀ τ n`.
2. Sign bound `|thetaSummand| ≤ exp(-π c ‖n‖² + 2π ‖n‖ ‖Im z‖)` checked.
3. Quasi-periodicity sign convention self-consistent; reindex `n ↦ n - m` confirmed matches Mumford Vol I §II.1.

## Lean 4 idiomaticity — cleanup targets

### #4-5: remove `intVecToC` + `let nC := …`

> "`@[simp] noncomputable def intVecToC` is not actually noncomputable (`Int.cast : ℤ → ℂ` is computable). Ad-hoc casting aliases fight the scalar tower. Inline `(n · : ℂ)`. And `let nC := …` inside a definition body creates a `letE` that blocks `simp`/`rw` in downstream proofs."

**Action:** delete `intVecToC`, inline casts, remove `let`.

### #6: `SiegelUpperHalfSpace` — use `Subtype`, not `structure`

> "Using a `structure` is a trap: you won't get an auto-inherited `TopologicalSpace`, `MetricSpace`, `NormedSpace` from `Matrix (Fin g) (Fin g) ℂ`. Switch to a `def` alias of a `Subtype` to pick those up for free."

**Action:** switch `SiegelUpperHalfSpace g` from `structure { val, isSymm, imPosDef }` to `def ... := { τ // τ.IsSymm ∧ (τ.map Complex.im).PosDef }`.

### #7-8: Siegel math is correct

- `IsSymm` (τ = τᵀ) is the right condition — Riemann's 1st bilinear relation gives symmetric, not Hermitian. Confirmed.
- `Matrix.PosDef` is the right predicate given `val.IsSymm` propagates to `(val.map Im).IsSymm`.

---

## Architectural concerns — address later

### #9 `NormedAddCommGroup` trap — LETHAL design flaw

> "`IsZLattice` demands `NormedAddCommGroup V` and `NormedSpace ℂ V`. But `HolomorphicOneForm X` is a finite-dim ℂ-space with **no canonical norm** until you define the Hodge inner product (which itself depends on the period matrix you're building!). Forcing a non-canonical norm on `HolomorphicOneForm X` via `FiniteDimensional.toNormedSpace` creates typeclass diamonds the moment you change bases or relate two curves."

> "Solution: drop `IsZLattice` if it strictly demands norm. State compactness/discreteness purely topologically (`DiscreteTopology L`, `CompactSpace (V ⧸ L.toAddSubgroup)`)."

**Implication for Part B.** `Jacobian X := ComplexTorus (HolomorphicOneForm X →ₗ[ℂ] ℂ) (periodLattice X)` is problematic because the ambient has no canonical norm. Two plausible responses:

- **Option A**: refactor `ComplexTorus` to drop `NormedAddCommGroup` requirement — build CompactSpace via a direct fundamental-domain argument without going through `IsZLattice.isCompact_range_of_periodic`.
- **Option B**: bite the bullet and transport the Jacobian to `Fin g → ℂ` via a chosen basis right at the `Jacobian X` definition. This gives up the "basis-free at the type level" design goal.

Both need thought. Option A is more work but preserves the design. Option B aligns with Gemini's #11 fix.

### #10 `Classical.choose` for charts

> "If you build charts via `Classical.choose`, proving `isManifold_of_contDiffOn` is a living hell. Chart transitions look like `s₂(x) − s₁(x)`, and proving this is locally constant (valued in L) requires algebraic control you don't have over opaque `Classical.choose` outputs."

**Partial pushback we can make.** We already proved `IsManifold` on `ComplexTorus V L`. The critical insight Codex used was to prove atlas-specific rewrite lemmas (`extChartAt_symm_eq_quotient_mk` + product variant) that expose the structure. So the concern is real but addressable — **provided** we maintain strong `simp`-normal-form lemmas for the chart data. Add to the plan: before any downstream module consumes `chartAt`, prove a comprehensive set of simp lemmas reducing it to its definitional form.

### #11 `ChartedSpace V` vs `ChartedSpace (Fin g → ℂ)` — dual instance problem

> "If you define `ChartedSpace V (ComplexTorus V L)` and then transport to `ChartedSpace (Fin g → ℂ)` via `Basis.equivFun`, you'll end up with *two* `ChartedSpace` instances on `Jacobian X`. Lean's typeclass inference picks one arbitrarily, leading to non-defeq chart failures when you try Buzzard's exact statement."

> "Solution: inject the basis into the `ComplexTorus` charts from the start. `def ComplexTorus (V : Type) ... (b : Basis (Fin g) ℂ V)` and build `OpenPartialHomeomorph` directly from `V/L` to `Fin g → ℂ` by composing the quotient lift with `b.equivFun`."

**Implication:** the current `ComplexTorus V L` is a design target for refactoring when we reach the Jacobian bridge. At Jacobian construction time, pick a basis `b : Basis (Fin g) ℂ V` once and thread it through. Aligns with Option B from #9.

---

## Triage

### Fix now (quick)

- [x] Delete `intVecToC`, inline cast, remove `let nC := …` in Theta.
- [x] Siegel as Subtype not structure.

### Record for Part B design (architectural)

- [ ] NormedAddCommGroup / IsZLattice tension at the `Jacobian X` bridge.
- [ ] Basis injection into `ComplexTorus` to avoid dual `ChartedSpace` instances.
- [ ] Strong simp-normal-form lemmas for `chartAt` / `extChartAt` data before consumers touch them.

Update `docs/formalization-plan.md` §5.1 (Jacobian/Construction) to reflect these two architectural concerns as they materially affect the bridge design.

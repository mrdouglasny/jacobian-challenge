# Gemini review of the axiom suite (2026-04-19)

Model: `gemini-3-pro-preview` via `chat_gemini` (Deep Think timed out after 5 min).

Request: adversarial review of the nine named axioms declared/stubbed in
`Jacobians/Axioms/` + `Jacobians/RiemannSurface/{Periods,IntersectionForm}.lean`.

## Top findings (severity order)

### 🔴 UNSOUND: `AX_FiniteDimOneForms` + `True ∧ True` stub + global instance

At the current scaffold, `HolomorphicOneForm X` is the coerced type of a
submodule with predicate `True ∧ True`, so it is ℂ-linearly equivalent to
the full function space `X → ℂ → ℂ`. Combined with the global
`FiniteDimensional ℂ (HolomorphicOneForm X)` instance and the fact that
`ConnectedSpace X` supplies `Nonempty X`, we can derive:

  1. Extract `x₀ : X` from `[Nonempty X]` (via `ConnectedSpace X`).
  2. The linear-equivalence transfer gives
     `FiniteDimensional ℂ (X → ℂ → ℂ)`.
  3. Evaluation at `x₀` is a surjective ℂ-linear map
     `(X → ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ)`, so `FiniteDimensional ℂ (ℂ → ℂ)`.
  4. Mathlib knows `Infinite ℂ` and `¬ FiniteDimensional 𝕜 (ι → 𝕜)` for
     `Infinite ι`, so `False`.

**Lethality:** typeclass inference can synthesise the contradiction during a
search, so an attacker could discharge all 24 Challenge sorries via
`exfalso`.

**Fix.** Two plausible routes:
  * (A) Replace the stub carrier with `⊥ : Submodule ℂ (X → ℂ → ℂ)` for
    now. `HolomorphicOneForm X ≃ 0`, genus = 0 everywhere, FD is
    trivial, no axiom needed. Deletes the unsoundness entirely; the
    `AX_FiniteDimOneForms` axiom + instance become dormant until the
    predicates are refined.
  * (B) Make `HolomorphicOneForm` genuinely opaque (new declaration, not a
    submodule coercion). More disruptive — requires restating the
    `AddCommGroup`/`Module ℂ` instances.

  (A) is simpler and keeps the plan's submodule-based story intact. Mark
  `AX_FiniteDimOneForms` "not yet needed" in docs.

### 🟠 MATH-WRONG: `AX_RiemannBilinear` target signature

Currently sketched as:
```
axiom AX_RiemannBilinear ... (α : Basis (Fin (2 * genus X)) ℤ (H1 X x₀))
    (ω : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
  ∃ τ : SiegelUpperHalfSpace (genus X), periodMatrix X x₀ α ω = [I | τ]
```

`[I | τ]`-normal form holds only when `α` is a **symplectic** basis of
`H_1` and `ω` is the basis of 1-forms **normalized** to have `A`-periods
equal to `I`. Universal quantification over arbitrary bases makes the
axiom false.

**Fix.** Shift existentials to cover the choice of bases:
```
∃ α : Basis (Fin (2 * genus X)) ℤ (H1 X x₀),
∃ ω : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X),
∃ τ : SiegelUpperHalfSpace (genus X),
  periodMatrix X x₀ α ω = [I | τ]
```

Or better: factor into (i) symmetric + `Im > 0` bilinear-form statement
basis-independent, (ii) `[I|τ]` as derived theorem via basis change.

### 🟠 SILENTLY VACUOUS: `AX_RiemannRoch` + `AX_SerreDuality` without FD hypotheses

`Module.finrank ℂ M = 0` when `M` is not finite-dim. Without
`[FiniteDimensional ℂ ...]` hypotheses, the Riemann-Roch equation reduces
to `0 - 0 = deg D + 1 - g` and becomes silently false, absorbed trivially.

Two fixes, both needed:
* Add `[FiniteDimensional ℂ (H0 X (O(D)))]` and `[FiniteDimensional ℂ
  (H1 X (O(D)))]` as hypotheses.
* Use `ℤ`-valued subtraction (`Module.finrank` is `ℕ`; `Nat.sub` truncates
  at 0 when negative, so `1 - 2 = 0` as ℕ, destroying the formula for
  divisors of small degree). Cast both sides to `ℤ`.

For `AX_SerreDuality`, strictly prefer the isomorphism statement:
```
H1 X (O(D)) ≃ₗ[ℂ] Module.Dual ℂ (H0 X (Ω¹ ⊗ O(-D)))
```
which implies the dimension equality AND transfers finite-dimensionality
in one go.

### 🟠 TOO WEAK: `AX_PeriodInjective`

`Function.Injective (periodMap X x₀)` is not enough to build
`Jacobian X` as a complex torus — the image of a ℤ-rank-2g group into
`ℝ^(2g)` under an injective map can still be dense. We need the image to
be a **ℤ-lattice** (discrete of full real rank).

**Fix.** Replace or augment with:
```
axiom AX_PeriodLattice {X} [...] (x₀ : X) :
    IsZLattice ℝ (LinearMap.range (periodMap X x₀))
```
This subsumes injectivity (by rank matching) and gives the exact
`IsZLattice` typeclass our `ComplexTorus V L` machinery demands.

### 🟡 INCOMPLETE: `AX_AbelTheorem`

`Function.Injective (ofCurve P₀)` is a corollary of Abel's theorem but not
its full content. The theorem's full content is: kernel of the Abel-Jacobi
map `Div(X) →+ Jacobian X` is exactly the principal divisors. Adequate
for Track 1 (Buzzard's 24 sorries) but Track 2 will stall without the full
kernel description.

Keep injectivity for now; plan upgrade to the kernel formulation when
Track 2 work begins.

### 🟡 `AX_BranchLocus` has `toFinset` hell

`(f ⁻¹' {q}).toFinset` needs `Fintype`/`Decidable`, dependent-type
spaghetti before we can state the axiom.

**Fix.** Use `tsum` with `localOrder f p q` extended to 0 for `p ∉ f⁻¹(q)`:
```
axiom AX_BranchDegree ... :
  ∃ d : ℕ, 0 < d ∧ ∀ q : Y, (∑' p : X, localOrder f p q) = d
```
Also replace `¬ ∀ x y, f x = f y` (non-constant-as-double-∀) with
`¬ ∃ c, ∀ x, f x = c` (the standard "non-constant" predicate).

### 🟡 CIRCULAR: `AX_H1FreeRank2g` vs fixed `AX_RiemannBilinear`

If the fixed `AX_RiemannBilinear` existentially asserts a symplectic basis
of `H_1` of the right index type, it implies free-abelian-rank-2g for
`H_1`, making `AX_H1FreeRank2g` redundant. Gemini recommends keeping them
separate for Lean ergonomics but decoupling structurally:
* 2a: `Module.Free ℤ (H1 X x₀)` (basepoint-free).
* 2b: `Module.finrank ℤ (H1 X x₀) = 2 * genus X` (Hodge identity).

### 🟢 Consistent on `ℙ¹`

The collection is mutually consistent on `X = ℙ¹` IF `SiegelUpperHalfSpace 0`
is inhabited (`0×0` matrix trivially `PosDef`). Verify this.

### 🟢 Missing axiom: intersection form on `H_1`

`AX_RiemannBilinear` talks about "symplectic basis", but we have not
axiomatized the non-degenerate alternating ℤ-bilinear intersection
pairing on `H_1`. Without it, "symplectic" has no formal meaning. This
is the missing prerequisite.

## Cross-cutting

### X1. Discharge priority (revised)

Gemini's recommended ordering (replacing ours):
1. `AX_FiniteDimOneForms` (infrastructure — most downstream depends on
   `genus` being nonzero).
2. `AX_H1FreeRank2g` (requires genus).
3. `AX_PeriodLattice` (requires both — defines the Jacobian quotient).
4. `AX_RiemannBilinear` (requires the Jacobian lattice).
5. `AbelTheorem`, `SerreDuality`, `RiemannRoch` (independent AG
   targets).

Our original "easy first" ordering was upside-down.

### X2. `axiom` as typed stub for not-yet-written `def`

Gemini initially flagged this as bad practice; on pushback conceded:
as long as the final `def`'s signature matches the `axiom`'s exactly,
replacing `axiom X : T` by `def X := ... : T` is a drop-in. Downstream
files don't break unless they used definitional equality (which they
can't, because axioms have no equational lemmas). The real risk is
signature drift when the `def` lands, which forces a refactor anyway.

Verdict: keep using `axiom` as a typed stub.

### X3. `opaque` vs `axiom`

For *data* stubs (e.g., `periodMap`), both work; `opaque` expects a
witness (even if bogus), `axiom` does not. For *propositional* stubs
(`AX_PeriodInjective`), `axiom` is the only right choice.

For the `HolomorphicOneForm X` unsoundness fix (finding 1), `opaque`
would be heavier than just replacing the stub submodule with `⊥`.

## Action items

(Ordered by impact.)

1. **(🔴 CRITICAL) Fix `HolomorphicOneForm` unsoundness.** Switch stub
   carrier to `⊥`, document the temporary `genus = 0` consequence.
   Inform review docs that the `AX_FiniteDimOneForms` instance is now
   dormant (trivially proved from `⊥`-submodule).
2. Add `AX_IntersectionForm` as a new named axiom, giving the
   non-degenerate alternating ℤ-bilinear pairing on `H_1`.
3. Update `AX_RiemannBilinear` target signature to shift existentials to
   cover basis choice.
4. Split `AX_H1FreeRank2g` into two pieces: free-abelian (basepoint
   structure) + rank-equals-2g (Hodge identity).
5. Update `AX_RiemannRoch` target signature with FD hypotheses and ℤ-valued
   LHS.
6. Update `AX_SerreDuality` target signature to the isomorphism form.
7. Update `AX_BranchLocus` target signature: `tsum` + `¬ ∃ c, ∀ x, f = c`.
8. Upgrade `AX_PeriodInjective` to `AX_PeriodLattice` (IsZLattice).
9. Document that `AX_AbelTheorem` is a partial-statement suitable for
   Track 1, full Abel-Jacobi kernel statement postponed to Track 2.
10. Re-order `docs/formalization-plan.md` §7 discharge priority list.

## Open questions for further review

* Concrete Lean exploit for finding 1 on the current code — I should
  verify with `lean_verify` / `lean_run_code` that `FiniteDimensional ℂ
  (HolomorphicOneForm X)` really composes with `LinearMap.surjective_range`
  to derive `False`.
* Whether switching to `⊥`-stub makes the `AX_FiniteDimOneForms` axiom
  and instance declaration pointless. If so, remove them; reintroduce
  when predicates are refined.

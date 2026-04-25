# Abel–Jacobi Plan (Path B)

Replace `ofCurve`, `periodLattice`, and (eventually) prove Abel's theorem. Goal: make `ofCurve_inj` and the lattice-preservation lemmas genuine theorems about genuine objects, not placeholders.

**Canonical reference**: Forster §§10–12 (line integrals) + §21 (Abel–Jacobi). Miranda Ch. IV §§3–4 + Ch. V §§2–3.

---

## Current state (end of Montel closure)

- `periodLattice X := Submodule.span ℤ (range (finBasis ℝ (Fin g → ℂ)))` — purely algebraic; no connection to periods of 1-forms.
- `ofCurve P := fun _ => 0` — constant zero; `ofCurve_inj` is `sorry`.
- `LineIntegral.lean` has `pathSpeed` + scalar `lineIntegral α γ : ℂ` for one form and one path.
- `FiniteDimensional ℂ (HOF X)` is real (post-Montel), so `genus X = finrank ℂ (HOF X)` is a meaningful ℕ.

## Target end state

- `periodLattice X : Submodule ℤ (Fin (genus X) → ℂ)` built from `∫_γ ω_•` over closed loops.
- `ofCurve P Q := [∫_{γ_{P→Q}} ω_•]` modulo period lattice, well-defined.
- `ofCurve_inj` proved (Abel's theorem).
- `ambient{Phi,Psi}_preserves_lattice` proved.

---

## Phase 1 — Line integral infrastructure (foundation)

Build the integration-as-function on the space of (form, path) inputs. Make the scalar line integral *usable* in downstream proofs.

### 1a. Vector line integral (the period map)

```lean
noncomputable def lineIntegralVec
    (ω : Fin (genus X) → HolomorphicOneForms X)
    (γ : ℝ → X) : Fin (genus X) → ℂ :=
  fun i => lineIntegral (ω i) γ
```

Trivial once `lineIntegral` is present. **Est: 10 lines.**

### 1b. Line integral algebraic properties

Essential identities proved for `lineIntegral`:
- Linearity in α: `lineIntegral (α + β) γ = lineIntegral α γ + lineIntegral β γ`.
- Scalar: `lineIntegral (c • α) γ = c • lineIntegral α γ`.
- Reversal: `lineIntegral α (reverse γ) = - lineIntegral α γ`.
- Concatenation: `lineIntegral α (γ ∗ γ') = lineIntegral α γ + lineIntegral α γ'`.

`lineIntegral α γ := ∫ t in 0..1, α(γ t)(γ'(t))`; linearity is just integral linearity; reversal/concatenation are standard substitution arguments. **Est: ~150 lines.**

### 1c. Path-independence inside a chart (Forster §10.5)

**Fact**: If γ, γ' are two smooth paths with same endpoints and IMAGE CONTAINED in a single chart domain, `lineIntegral α γ = lineIntegral α γ'` (by Cauchy's theorem on the chart image).

This is the local content that globalizes (via overlap) to "path independence modulo homotopy".

**Est: ~200 lines**, nontrivial because it needs Cauchy for a polygon in a simply-connected chart.

---

## Phase 2 — Period lattice as real object

### 2a. Period lattice definition

```lean
/-- The period lattice as the ℤ-span of `lineIntegralVec ω` over
smooth closed loops based at some basepoint. -/
noncomputable def periodLattice (X : Type*) [...] : Submodule ℤ (Fin (genus X) → ℂ) :=
  Submodule.span ℤ
    { v : Fin (genus X) → ℂ | ∃ (γ : ℝ → X),
        ContMDiff ... γ ∧ γ 0 = basepoint ∧ γ 1 = basepoint ∧
        v = lineIntegralVec (Module.finBasis ℂ (HOF X)) γ }
```

Where `basepoint : X` is chosen via `Classical.arbitrary` (manifold is `Nonempty`).

**Independence from basepoint**: the set of periods is the same up to basepoint choice, because for any other basepoint Q, a loop at Q equals a loop at P conjugated by a path from P to Q, and the integral is conjugation-invariant (modulo periods).

**Est**: definition ~20 lines; basepoint-independence ~100 lines if proven.

### 2b. Discrete / lattice instances

**CRITICAL BLOCKER**: The real period lattice has rank 2·(genus X) in ℂ^(genus X) as a ℤ-module. Showing this requires:
- Hodge decomposition: `H^1(X, ℂ) ≃ HOF ⊕ HOF‾`.
- Non-degeneracy of the period pairing.
- Sometimes Poincaré duality + cup product.

This is **weeks to months** of Mathlib-adjacent work and is itself a significant contribution.

**Two pragmatic options:**

**Option (i): Accept the lattice instances as separate axioms/sorries.**
Keep `periodLattice` as defined, add a `LatticeHypothesis` typeclass (or `class IsPeriodLattice`) bundling the two missing instances (`DiscreteTopology`, `IsZLattice ℝ`). Then `Jacobian`, functoriality lemmas, etc., assume this class.

```lean
class IsPeriodLattice (X : Type*) [...] : Prop where
  is_lattice : DiscreteTopology (periodLattice X)
  is_full : IsZLattice ℝ (periodLattice X)
```

This isolates the Hodge-level content as a single named open problem, keeping everything else real.

**Option (ii): Prove rank 2g via Hodge theory.**
Massive. Requires: de Rham cohomology on compact manifolds, Hodge decomposition for complex structure, period pairing is a perfect pairing. Each of these is Mathlib-contribution-sized.

**Recommendation: Option (i)**, with a clearly-labelled axiomatic `IsPeriodLattice` class. Tag it as "Hodge decomposition gap" in STATUS so future work can close it.

### 2c. Period-lattice membership of closed-loop integrals

`∫ over a closed loop ∈ periodLattice` by definition. Useful simp lemma. **Est: ~30 lines.**

---

## Phase 3 — Real `ofCurve`

### 3a. Path existence

For P, Q in X (connected, path-connected as a manifold), ∃ smooth path γ with γ 0 = P, γ 1 = Q. Needs:
- `PathConnectedSpace X` (follows from `ConnectedSpace + LocPathConnectedSpace`; manifolds are `LocPathConnected`).
- Smooth approximation of a continuous path. Depends on Mathlib's `ContMDiffMap`; may need to build a specific "smooth path from P to Q" construction via chart-by-chart linear interpolation.

**Est**: ~150 lines (nontrivial; smooth path construction via partition-of-unity-style glueing).

### 3b. `ofCurve` definition

```lean
noncomputable def ofCurve (P : X) (Q : X) : Jacobian X :=
  QuotientAddGroup.mk <|
    lineIntegralVec (Module.finBasis ℂ (HOF X)) (Classical.choose (exists_smooth_path P Q))
```

**Well-definedness**: path independence modulo periods. For two paths γ, γ' from P to Q, concatenate γ ∗ (reverse γ'); this is a closed loop at P; its integral is in the period lattice (by 2c). Hence `∫_γ - ∫_{γ'} ∈ periodLattice`, same quotient class.

**Est**: definition ~20 lines; well-definedness proof ~100 lines (uses 1b + 2c).

### 3c. `ofCurve_self`, `ofCurve_contMDiff`

- `ofCurve P P = 0`: take constant path at P; integral is 0.
- `ContMDiff (ofCurve P)`: Q ↦ ∫_{γ_{P→Q}} is smooth in Q. Nontrivial — depends on how the path depends on Q. Classical approach: fix a local chart around Q, use a chart-specific smooth path from a reference point to Q within the chart.

**Est**: `ofCurve_self` ~10 lines; `ContMDiff` ~200 lines (hardest piece of this phase).

---

## Phase 4 — Lattice-preservation lemmas

### 4a. `ambientPhi_preserves_lattice`

Claim: `ambientPhi f hf : (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ)` sends `periodLattice X` into `periodLattice Y`.

**Mathematical content**: `ambientPhi` is the pushforward-of-forms map (dualized to period coordinates); it sends "integral over a loop in X" to "integral over the image loop in Y". Both are in the period lattices.

Specifically, for γ : loop in X with basepoint P, `f ∘ γ : loop in Y` with basepoint `f P`. Up to basepoint-change (Phase 2a independence), `ambientPhi (∫_γ ω_X) = ∫_{f∘γ} ω_Y ∈ periodLattice Y`.

**Est**: ~200 lines. Nontrivial because `ambientPhi` is currently defined algebraically via matrix transpose; need to match it to the pushforward-of-forms interpretation.

### 4b. `ambientPsi_preserves_lattice`

Symmetrically for pullback. **Est**: ~200 lines.

---

## Phase 5 — Abel's theorem (the capstone)

### 5a. Divisor theory on compact Riemann surfaces

**Prerequisites** (not in Mathlib):
- `MeromorphicFunction X : Type` — meromorphic functions on compact Riemann surface.
- `Divisor X : AddGroup` — formal ℤ-linear combinations of points; `div f` of a meromorphic f.
- Degree of divisor: `deg : Divisor X →+ ℤ`; `deg (div f) = 0` (because f has equal zeros and poles by argument principle).
- Principal divisors form a subgroup; `Div X / PrincipalDivisors X = Pic X` (Picard group).

**This is itself a significant Mathlib-sized contribution**. Estimated in thousands of lines.

### 5b. Abel's theorem statement and proof

**Statement** (Forster 21.4): A divisor D of degree 0 is principal ⇔ its Abel-Jacobi image is zero in the Jacobian.

Given Abel's theorem + 5a divisor infrastructure, `ofCurve_inj` follows: `ofCurve P Q = ofCurve P Q'` ⇒ `Q - Q'` principal (Abel). But for genus ≥ 1, a principal divisor of the form `Q - Q'` with Q ≠ Q' gives a meromorphic function with a simple pole at Q' and simple zero at Q — such a function makes X biholomorphic to ℂP¹ (genus 0). Contradiction with `0 < genus X`. Hence Q = Q'.

**Est**: divisor infrastructure + Abel ≈ **6–12 months of sustained work**.

---

## Suggested sequencing

**Near-term (1–2 sessions each):**
1. Phase 1a (vector line integral) — 30 min.
2. Phase 1b (linearity, reversal, concatenation) — 2–3 sessions.
3. Phase 1c (chart-local path independence) — 2–3 sessions.
4. Phase 2a (period lattice definition) — 1 session.
5. Phase 2b **Option (i)** (`IsPeriodLattice` typeclass with axiomatic instances) — 1 session.

At this point the period lattice is a real object, typeclass-axiomatized.

**Medium-term (3–6 sessions):**
6. Phase 2c (period membership for closed loops) — 1 session.
7. Phase 3a (smooth path existence) — 2–3 sessions.
8. Phase 3b (real `ofCurve` definition + well-definedness) — 2 sessions.
9. Phase 3c (`ofCurve_self`, `ContMDiff`) — 3–4 sessions for ContMDiff.

At this point `ofCurve` is real; `ofCurve_self` closes. `ofCurve_contMDiff` is a real theorem.

**Long-term:**
10. Phase 4 (lattice preservation) — 2–3 weeks total.
11. Phase 5 — months, not appropriate for current scope.

---

## Explicit non-goals / gaps

Items that stay `sorry` / axiomatic indefinitely at the end of Phases 1–4:
- `IsPeriodLattice X` (Hodge decomposition / rank = 2g).
- `ofCurve_inj` (needs Phase 5 / Abel).
- `genus_eq_zero_iff_homeo` (uniformization).

The STATUS.md after Phase 4 completion would read: "Abel-Jacobi machinery in place modulo Hodge decomposition (1 axiom) and Abel's theorem (ofCurve_inj sorry). Challenge headline uses real objects, not placeholders."

---

## What to start with, concretely

Phase 1a + 1b (vector line integral + linearity/reversal/concatenation) — this is bounded, useful, has no Mathlib gaps, and feeds directly into everything else. It's also a nice warm-up after the bundle-machinery work of Path 2.

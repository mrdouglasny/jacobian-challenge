# `riemannRochSpace_finiteDimensional` — discharge plan

**Statement.** On a compact connected Riemann surface `X`, the Riemann–Roch
space `L(D) = riemannRochSpace D = { meromorphic f : ord_p f ≥ -D(p) ∀ p }`
is finite-dimensional over ℂ, for **every** divisor `D`:
```lean
@[instance] axiom riemannRochSpace_finiteDimensional {X} [compact RS X]
    (D : Divisor X) : FiniteDimensional ℂ (riemannRochSpace D)
```
**Location:** `Jacobians/RiemannSurface/Cohomology/RiemannRochAPI.lean:123`.
`riemannRochSpace` is the de-opaqued, vetted-faithful germ-quotient model of
`L(D)` (`RiemannRochSpace.lean:294`); `MeroField X = MeroFunctions X ⧸ GermZero X`.

**Leverage.** This pin fills the `[FiniteDimensional H0]` instance bracket that
`AX_RiemannRoch` consumes (H0 directly: `H0 (O_D) = riemannRochSpace D`); the
`[FiniteDimensional H1]` bracket is **derived** (`AX_SerreDuality` gives
`H¹(O_D) ≃ₗ Dual (H⁰(O(K−D)))`, and `L(K−D)` is finite by the same result). So
discharging this single axiom completes the **entire finiteness layer** of the
RR/Serre anchor — the H0 *and* H1 finite-dimensionality that every dimension
count rests on, and the sorries at `RiemannRochAPI.lean:202` (`h0_of_deg_gt`),
`:212` (`h0_point_eq_one_of_genus_pos`), and (transitively, via the Serre-derived
H1 instance) `SerreDualityAPI.lean:92` (`h1_eq_zero_of_deg_gt`).

**Route:** elementary `ℓ(D) ≤ 1 + deg D⁺` (Montel-free; the deep analytic
ingredient is already proved). **Effort:** ~5–8 focused days (Codex).
**Vetted:** Gemini deep-think (math) + Codex (Lean route), both **confirm**.

---

## Decision: ELEMENTARY route, not the Montel re-target

The previous draft of this plan proposed **re-targeting the vendored Kirov Montel
engine** (which proves `dim H⁰(Ω¹) < ∞` for holomorphic 1-forms) from the
cotangent bundle to `O_D`. **Two investigations + external vetting overturned
that.** The right route is the elementary "easy half of Riemann's inequality"
upper bound `ℓ(D) ≤ 1 + deg(D⁺)`, which is **Montel-free** and reuses
infrastructure the project already has sorry-free.

### Why not Montel (engine map, 2026-06-08)

- The Kirov engine (`Vendor/Kirov/Montel.lean` + `Montel/*`) is **hard-wired to
  the cotangent bundle**: the norm (`supNormK`/`chartNormK`/`localRep`), its
  positive-definiteness, and the holomorphy bridge are all written against
  `ContMDiffSection` of the *tangent* bundle. Only two pure-ℂ lemmas
  (`exists_cauchy_deriv_bound`, `analyticOn_of_tendstoLocallyUniformlyOn`) and
  Mathlib's Riesz `of_isCompact_closedBall₀` are reusable; the Riesz core is
  Mathlib's, not Kirov's.
- **Fatal mismatch:** the entire Montel scaffold rests on *bounded holomorphic*
  ⇒ Cauchy estimate ⇒ equicontinuous ⇒ Arzelà–Ascoli. Elements of `L(D)` are
  **unbounded at their poles**, so `(∀ z ∈ U, ‖f z‖ ≤ C)` fails on any chart
  meeting `supp(D)`. Re-targeting would require defining a Hermitian metric on
  `O(D)` that vanishes at the poles (to get a bounded sup-norm) — a monumental
  detour to prove a 1-dimensional fact. "Re-target Kirov" badly understates this:
  it is **writing a second, analytically harder Montel engine**.
- Gemini deep-think (below) confirms: the Montel/∂̄ machinery is the universal
  hammer for `dim H⁰(O(D)) < ∞` on *higher-dimensional* manifolds (where the
  polar set is a hypersurface and one cannot "induct over points"). **On a
  curve** the polar set is finite and the elementary induction bypasses it.

### Keep the Montel engine anyway (scope note)

Discharging *this* axiom Montel-free does **not** make the Kirov engine
disposable. The eventual discharge of **`AX_SerreDuality`** (a separate pinned
axiom) needs the closed-range / Schwartz-compact-operator property of `∂̄`,
which *is* where Montel is unavoidable. So: elementary route here; Montel stays
for the Serre-duality discharge later. (Today H1-finiteness is derived from the
`AX_SerreDuality` *axiom*, so the elementary L(D) result is sufficient now.)

---

## The elementary route (the plan)

Target: `FiniteDimensional ℂ (riemannRochSpace D)` for all `D`, with the
quantitative bound `Module.finrank ℂ (L D) ≤ 1 + (Divisor.deg X Dᐩ).toNat`.

**Step 1 — reduce to effective `D`.** `L(D) ⊆ L(Dᐩ)` where `Dᐩ` is the positive
part (`D ≤ Dᐩ` coefficientwise ⇒ the order condition is weaker). A `Submodule`
of a finite-dimensional space is finite-dimensional. (`D` is a divisor = finite
support, so any `f ∈ L(D)` is automatically holomorphic off the finite set
`supp(D)` — **no separate "finitely many poles" theorem is needed**.)

**Step 2 — induction adding one point.** For an effective divisor `D'` and a
point `p`, set `n = (D' + p) p` (the new pole bound). Define the **single
local-coefficient functional**
```
φ : L(D' + p) → ℂ,   φ(f) = regularValue_p ( wⁿ · f )
```
where `w` is the **local chart coordinate at `p`** (NOT a global meromorphic
uniformizer — we do not have one). Since `ord_p(wⁿ·f) = n + ord_p(f) ≥ 0`, the
germ `wⁿ·f` is holomorphic at `p` and `regularValue_p` cleanly extracts its
value (= the `a₋ₙ` Laurent coefficient of `f`, but we never name coefficients).
- **ℂ-linear:** multiplication by `wⁿ` and `regularValue_p` (on order-≥0 germs)
  are ℂ-linear.
- **Kernel:** `φ(f) = 0 ⇔ ord_p(wⁿ·f) ≥ 1 ⇔ n + ord_p(f) ≥ 1 ⇔
  ord_p(f) ≥ -(n-1) = -D'(p)`, and the conditions at every other point are
  unchanged, so `ker φ = L(D')`. Hence `dim L(D'+p)/L(D') ≤ 1`.

Gemini's cleaner phrasing (avoids Laurent coefficients entirely): work in the
local fraction field `𝓜_p`; everything in Step 2 is **purely local at `p`**, so
the germ-quotient model's lack of a global identity principle is irrelevant.

**Step 3 — base case.** `L(0) = ℂ` (constants). **Already a theorem**
(`h0_zero`, via `exists_const_mk_eq_of_mem` + `regularValue` +
`liouville_compact_complex_manifold_for_h0`, all sorry-free).

**Step 4 — assemble.** The SES extension principle
`Module.Finite.of_submodule_quotient` (submodule `L(D')` finite-dim by IH +
quotient `L(D'+p)/L(D')` finite-dim ⇒ `L(D'+p)` finite-dim), inducting over the
effective divisor **reindexed as a `Multiset X`** (`Multiset.induction_on`; cons
= adding one point — *not* a `FreeAbelianGroup`/degree induction), gives the
result; `finrank_quotient_add_finrank` yields the `≤ 1 + deg D⁺` bound; Step 1
covers general `D` via `FiniteDimensional.finiteDimensional_submodule`.

> **Implementation note (Codex):** `φ` is a **new local wrapper**, not the
> project's `regularValue` (which is `private` + globally-scoped). Build it from
> Mathlib's `tendsto_nhds_of_meromorphicOrderAt_nonneg` on the chart pullback
> `twist f := fun z => (z - z0)^n * (f) (e.symm z)` with `e = chartAt ℂ p`,
> `z0 = e p` — working with the local `ℂ → ℂ` function near `z0`, never a global
> `X → ℂ` rep. ℂ-linearity is proved directly (uniqueness of limits +
> `Tendsto.add`/`smul`); the kernel identity uses `meromorphicOrderAt_mul`,
> `meromorphicOrderAt_pow_id_sub_const`, `tendsto_zero_iff_meromorphicOrderAt_pos`.

### Reusable (already sorry-free) vs new

| Ingredient | Status |
|---|---|
| `L(0) = ℂ` (holomorphic-on-compact-connected ⇒ constant) | **have** — `h0_zero`, `liouville_compact_complex_manifold_for_h0` (the deep analytic half — sorry-free) |
| order API + arithmetic (`meromorphicOrderAt_mul`, `meromorphicOrderAt_pow_id_sub_const`, `tendsto_zero_iff_meromorphicOrderAt_pos`, `tendsto_nhds_of_meromorphicOrderAt_nonneg`) | **Mathlib** — `Analysis/Meromorphic/Order.lean:202, 244, 371, 429` |
| chart bridges (`orderAt_eq_chartAt`, `…_of_mem_maximalAtlas`) | **have** — `Vendor/Wallace/.../VanishingOrder.lean:135, 342` |
| submodule-of-fin-dim is fin-dim (Step 1) | **Mathlib** — `FiniteDimensional.finiteDimensional_submodule` |
| SES fin-dim extension + bound (Step 4) | **Mathlib** — `Module.Finite.of_submodule_quotient`, `finrank_quotient_add_finrank` |
| **the local functional `φ` (chart pullback `(z−z0)ⁿ·f∘e.symm`, limit) + ℂ-linearity + `ker φ = L(D')`** | **NEW — the core new lemma** (`regularValue` is a *precedent* but private+global; build a fresh local wrapper) |
| **effective divisor reindexed as `Multiset X` + `Multiset.induction_on`** | **NEW — friction point** (`divOfMultiset`, `Finsupp.toMultiset` bridges) |

The hard analytic half (the Liouville endgame `L(0)=ℂ`) is **done sorry-free**;
the new work is order-arithmetic + one local-coefficient functional + a multiset
induction. **Codex estimate: 5–8 focused days.**

---

## Vetting

### Gemini deep-think (2026-06-08) — strategy + correctness: **CONFIRMED**

> "Your proposed elementary route is brilliant, mathematically flawless, and
> perfectly suited for Lean. You should absolutely use it for L(D)."

- **(a) correct & complete** — standard upper-bound proof, no gaps; `D` finite
  support bakes in the finite-pole fact.
- **(b)** `dim L(D) < ∞` (upper bound) is **genuinely independent** of §14
  `dim H¹(X,O) < ∞`; the deep theory is needed only for the *lower* bound /
  Riemann–Roch *equality* (existence of non-constant functions).
- **(c)** the Montel plan was higher-dimensional thinking (hypersurface polar
  sets); on a curve the elementary induction is strictly better and avoids
  Hermitian line-bundle metrics.
- **(d)** germ-quotient model is a **perfect fit** — Step 2 is purely local in
  `𝓜_p`; the absent global identity principle is irrelevant.
- **(e)** cleaner Step 2 via a uniformizer + `regularValue_p(zⁿ·f)`, kernel by
  order arithmetic (adopted above, with `z` = the chart coordinate).
- **(f) correction folded in:** do **not** discard Montel — it is required to
  *prove* `AX_SerreDuality` (closed-range of `∂̄`). It is just not needed for
  *this* axiom. (See "Keep the Montel engine" above.)

### Codex (GPT-5.4) — Lean-implementation reality check (2026-06-08): **CONCUR, ~5–8 days**

> "Concur: the elementary local-coefficient induction is the right route;
> retargeting the cotangent/bounded Montel engine is strictly worse here."

Concrete implementation guidance (verified against the Mathlib pin):

- **Mathlib lemmas confirmed present** — Step 1: `FiniteDimensional.finiteDimensional_submodule`; Step 4: `Module.Finite.of_submodule_quotient` + `finrank_quotient_add_finrank` (for the `≤ 1 + deg D⁺` bound).
- **Do NOT reuse `regularValue` directly for `φ`.** It is `private` and has a *global* signature `regularValue (f : MeroFunctions X) (h_nonneg : ∀ p, 0 ≤ orderAt p f) (p) : ℂ` — too global (in the induction step `wⁿ·f` is repaired only at the added point `p`; `f ∈ L(D'+p)` keeps its other allowed poles). Build a **local wrapper** from Mathlib's `tendsto_nhds_of_meromorphicOrderAt_nonneg` (`Mathlib/Analysis/Meromorphic/Order.lean:202`) on the chart pullback:
  ```lean
  let e := chartAt ℂ p; let z0 := e p
  let twist (f : MeroFunctions X) : ℂ → ℂ := fun z => (z - z0)^n * (f : X → ℂ) (e.symm z)
  ```
  `chartAt ℂ p` is the right chart API; do **not** form a global `X→ℂ` rep of `wⁿ·f` (MeroFunctions requires meromorphy everywhere) — work with the local `ℂ→ℂ` `twist` near `z0`. Chart bridges: `orderAt_eq_chartAt` (VanishingOrder.lean:135), `orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas` (:342).
- **Hardest sub-lemma = the kernel identity** `localCoeff p n F = 0 ↔ (-(n)+1) ≤ orderAtField p F` (under `F ∈ L(D'+p)`), via `meromorphicOrderAt_mul`, `meromorphicOrderAt_pow_id_sub_const`, `tendsto_zero_iff_meromorphicOrderAt_pos` (Order.lean:429, :371, :244). **No existing `regularValue`-linearity lemma** — prove `φ`'s ℂ-linearity directly from uniqueness of limits + `Tendsto.add`/`smul`. Also: well-definedness under `GermZero`.
- **Effective-divisor induction = reindex by `Multiset X`** (NOT a `FreeAbelianGroup`/`Finsupp`/degree induction — `Finsupp.induction_on` doesn't exist; degree induction is painful). Define `divOfMultiset s := (s.map FreeAbelianGroup.of).sum`, prove finiteness by `Multiset.induction_on`, then show every effective `D` equals `divOfMultiset` of its coefficient multiset (bridges `Finsupp.toMultiset`/`Multiset.toFinsupp`, `FreeAbelianGroup.equivFinsupp`).
- **Effort: 5–8 focused days** (2–4 for `φ` + kernel, 1–2 for the multiset/effectivity algebra, 1 for positive-part inclusion + assembly, + build/debug margin). Riskiest piece: the local functional on the germ quotient (well-definedness under `GermZero` + the kernel/order-arithmetic lemma).

---

## Build order (concrete first steps)

1. **`L(D) ⊆ L(D')` for `D ≤ D'`** + `FiniteDimensional.finiteDimensional_submodule` ⇒ the "reduce to effective + `L(D) ⊆ L(D⁺)`" plumbing. (Cheap; warms up the order-condition API.)
2. **The local functional `φ` and its kernel** — the core. Define `twist`/`localCoeff p n` via the chart pullback + `tendsto_nhds_of_meromorphicOrderAt_nonneg`; prove ℂ-linearity (limit uniqueness) and the kernel identity `localCoeff p n F = 0 ↔ -(n−1) ≤ orderAtField p F` (order arithmetic). This is the riskiest piece — do it first against a single fixed `D'+p` before wiring the induction.
3. **`Multiset X` reindexing** — `divOfMultiset`, the effective-divisor ↔ multiset bridge, and the one-point inclusion `L(divOfMultiset s) ⊆ L(divOfMultiset (p ::ₘ s))`.
4. **Assemble** — `Multiset.induction_on` + `Module.Finite.of_submodule_quotient`, base `h0_zero`; optionally carry the `finrank ≤ 1 + deg D⁺` bound via `finrank_quotient_add_finrank`.
5. **Replace the axiom** with the resulting `@[instance] theorem`; rebuild + `#print axioms` to confirm standard-3; update `AXIOM_AUDIT.md` + the README counts (42 → 41) + close the tracker issue.

## References

- Otto Forster, *Lectures on Riemann Surfaces* (GTM 81), §16 (the elementary
  `ℓ(D)` bound is the easy half of Riemann–Roch); §14 (the Montel/∂̄ finiteness
  theorem we are deliberately **not** using here). `refs/forster-riemann-surfaces/`.
- Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. VI (Riemann
  inequality, the `ℓ(D) ≤ deg D⁺ + 1` upper bound elementarily).
- Project precedents: `RiemannRochAPI.lean` (`regularValue`, `h0_zero`,
  `liouville_compact_complex_manifold_for_h0`); `RiemannRochSpace.lean` (model,
  order API). Engine map of why Montel is the wrong tool: investigation
  2026-06-08 (`Vendor/Kirov/Montel.lean` is cotangent-hard-wired + bounded-only).

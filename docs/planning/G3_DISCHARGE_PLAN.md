# G3 — derive "genus>0 ⇒ injective Abel" properly (no new axiom)

*2026-05-31. Milestone G3 of [`OFCURVE_INJ_DISCHARGE_PLAN.md`](OFCURVE_INJ_DISCHARGE_PLAN.md):
turn the general `AX_ofCurve_inj` (all genus>0) into a derived theorem. User
mandate (2026-05-31): derive G3 **properly** from `AX_RiemannRoch` + vendored
analytic infra — do **not** introduce a fresh divisor axiom. Homotopy
invariance (Fork 1) stays parked — see [[defer-homotopy-invariance]].*

## The target

```lean
-- the general statement, currently an axiom (AbelJacobiMap.lean:289)
theorem AX_ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurveImpl X P)
```

Route (Abel): `ofCurve P Q₁ = ofCurve P Q₂` →[G1] `abelJacobiDiv ((Q₁)−(Q₂)) = 0`
→[G2 = `AX_AbelTheorem`] `(Q₁)−(Q₂) ∈ PrincipalDivisors` →[**G3**] `Q₁ = Q₂`.

**G3 proper:** `genus X > 0 ⇒ ∀ Q₁ Q₂, (Q₁)−(Q₂) ∈ PrincipalDivisors → Q₁ = Q₂`.

## The blocking reality (why the old one-line sketch is not executable)

`Jacobians/RiemannSurface/LineBundle.lean` makes **opaque axioms** of:
`PrincipalDivisors`, `LineBundle`, `LineBundle.ofDivisor`, `H0`, `H1`. They
have **no function-space content** — there is no `div : MeromorphicFunction →
Divisor`, no `f ∈ H0 ↔ div f + D ≥ 0`. `AX_RiemannRoch` only relates their
`finrank`s. So "f with `div f = (Q₁)−(Q₂)`" and "`h⁰((Q₂)) = 1`" are currently
**unstatable**. G3 proper therefore REQUIRES first giving these stubs real
content. That de-opaquing is the bulk of the work; the genus obstruction is the
deep core.

Second fact (drives the architecture): RR+Serre numerics pin `h⁰(P)=1` only for
**g=1** (`deg(K−P)=2g−3 < 0` ⇒ `h⁰(K−P)=0`). For **g≥2** the proof needs the
GEOMETRIC fact *single simple pole ⇒ degree-1 map to ℙ¹ ⇒ biholomorphism ⇒
genus 0* — which routes through vendored Wallace
`weightedFiberConservation_of_contMDiff` (conservation of number), **not** RR.
So the irreducible hard core is geometric, and RR is used only for the
finrank/`h⁰` bookkeeping in the clean route.

## Available infra (don't rebuild)
- **Wallace `orderAt p f : WithTop ℤ`** (`Vendor/Wallace/.../VanishingOrder.lean`) —
  chart-independent vanishing/pole order of `f : X → ℂ` at `p`. Sorry/axiom-free.
- **Wallace `weightedFiberConservation_of_contMDiff`** (`HolomorphicMap.lean:1199`) —
  conservation of number / degree well-defined for `f : X → ℙ¹`. Standard-3.
- `Divisor X = FreeAbelianGroup X` (real); `Divisor.deg` (real `→+ ℤ`).
- `genus X` (real, via `finrank HolomorphicOneForm`).
- `AX_RiemannRoch`, `AX_SerreDuality` (axioms, keep).
- `abelJacobiDiv = FreeAbelianGroup.lift (ofCurveImpl · (arbitrary))`; `AX_AbelTheorem`.

## Milestones (each independently checkpointed for plan-loop)

### Phase S — strategy vet (DONE 2026-05-31, Gemini deep-think)
- **S1. VERDICT (Gemini DT, 2m42s):** strategy "geometrically completely sound."
  - (a) CONFIRMED: g≥2 unavoidably needs the geometric degree-1⇒biholo argument;
    RR+Serre numerics give `h⁰(P)=1` only for g=1 (`deg(K−P)=2g−3<0`). For g≥2,
    `h⁰(K−P)=g−1` ⟺ canonical system base-point-free ⟺ exactly the geometric
    "no degree-1 map" fact. **BONUS: G3 does NOT use `AX_RiemannRoch` at all** —
    it's entirely the meromorphic/analytic infra. ⇒ **Phase L dropped.**
  - (b) CONFIRMED: de-opaque div + geometric C1 is the optimal minimal-axiom
    decomposition; cannot stay inside opaque H⁰ (can't evaluate to build X→ℙ¹).
  - (c) Risk ranking (hardest first): **[NEW, was missing] constructing X→ℙ¹
    from f** (glue f and 1/f; tedious — axiomatize candidate) > finiteness of
    zeros/poles (Identity Thm + compactness, medium) > genus biholo-invariance &
    `genus ℙ¹=0` (medium; pullback iso of Ω¹) > **bijective⇒biholo: use the
    IFT optimization** (deg 1 ⇒ local mult 1 ⇒ deriv≠0 ⇒ local diffeo ⇒ global;
    do NOT prove general open-mapping/Osgood) > weight-1⇒injective (trivial Σmₓ=1).
  - (d) Connectedness essential (have it); match Wallace multiplicity to `orderAt`
    (zero-order at finite w, pole-order at ∞); `f≠0` globally suffices (connected).
  - **Recommended axiom boundary (3 standard analytic axioms):** (1) meromorphic
    f ⇒ holomorphic `f̂ : X→ℙ¹` with local winding = order of `(f−w)` / pole-order
    at ∞; (2) `genus ℙ¹ = 0`; (3) genus biholo-invariant. With these + Wallace
    conservation, G3 derives with NO Riemann-Roch dependency.
  - **HUMAN FORK (axiom boundary):** prove vs axiomatize each of the 3. Each is a
    standard fact; (1) is the tedious one most worth axiomatizing. Parked for MRD.

### Phase D — de-opaque the function/divisor layer (real content, no new axioms)
- **D1.** `MeromorphicFunctionField X` — nonzero meromorphic functions on `X` as a
  `CommGroup` under ×, built on Wallace `MeromorphicAtX` (global meromorphy).
  Companion: the constants `ℂˣ ↪`. *Finiteness lemma:* a nonzero global
  meromorphic function on compact `X` has finite zero/pole set (discreteness of
  zeros + compactness) — needed for `div` to land in `FreeAbelianGroup`.
- **D2.** `divHom : MeromorphicFunctionField X →+ Divisor X`, `f ↦ Σ_p orderAt p f · (p)`
  (well-defined by D1 finiteness; `div(fg)=div f+div g` from `orderAt` additivity).
- **D3.** **De-opaque `PrincipalDivisors`:** replace the opaque axiom with
  `PrincipalDivisors X := divHom.range`. Retires one axiom. `AX_AbelTheorem`
  keeps its statement verbatim. (Audit: −1 axiom.)

### Phase L — DROPPED (Gemini S1: G3 needs no Riemann-Roch)
The opaque `H0`/`LineBundle`/`AX_RiemannRoch` interface is NOT on the G3 path.
Leave those stubs untouched for now (they still serve `AX_SerreDuality` etc.).

### ℙ¹ / conservation infra (scoped 2026-05-31)
- `ProjectiveLine := OnePoint ℂ` (`Line.lean:38`) — Riemann sphere, pts `↑(z:ℂ)`
  or `∞`; `ChartedSpace ℂ` (2 charts) + `IsManifold`. Maps via coe `ℂ→ℙ¹` and `w↦↑w⁻¹`.
- **`genus ProjectiveLine = 0` ALREADY PROVEN, axiom-free** (`Line/Genus.lean:30`).
  ⇒ C1c half-done; only genus-biholo-invariance remains.
- Wallace `weightedFiberConservation_of_contMDiff` (`HolomorphicMap.lean:1199`):
  for `f:X→Y` ContMDiff, nonconstant, finite fibers, `∀ᶠ y in 𝓝 y₀,
  Σ_{fiber y} mapAnalyticOrderAt f = Σ_{fiber y₀} …` (LOCAL constancy). Upgrade to
  GLOBAL via ℙ¹ connectedness (locally-const ℤ on connected ⇒ const).
- `mapAnalyticOrderAt f p : ℕ` (`HolomorphicMap.lean:175`) — positive local mult.
  **C0 crux:** match `mapAnalyticOrderAt (toP1 f)` to `orderAt p f` (pole ⇒ fiber ∞).

### Phase C — the genus obstruction (deep core; no RR)
- **C0 [NEW, the tedious bridge].** `toP1 : MeromorphicFunctionField X → (X → ℙ¹(ℂ))`,
  `f ↦ f̂` holomorphic, gluing `f` (off poles) and `1/f` (off zeros), with local
  winding of `f̂` at `w` = `orderAt(·, f−w)` (finite `w`) / pole-order at `∞`.
  **Most likely axiom (Gemini-flagged tedious).** → human fork.
- **C1.** *degree-1 ⇒ genus 0.* Nonconstant `f` with `div f = (Q₁)−(Q₂)`, `Q₁≠Q₂`
  ⇒ `f̂` has total pole order 1 ⇒ degree 1 (Wallace conservation) ⇒ the `∞`-fiber
  is a single point of multiplicity 1. Then:
  - **C1a (trivial).** weight-1 fiber `Σ mₓ = 1`, `mₓ≥1` ⇒ `|fiber| = 1` (everywhere).
  - **C1b (IFT, NOT open-mapping).** local mult 1 ⇒ `f̂` derivative ≠ 0 ⇒ local
    diffeo (inverse function thm); bijective + local diffeo ⇒ global biholo.
  - **C1c.** `genus` biholo-invariant + `genus ℙ¹ = 0` ⇒ `genus X = 0`. Both are
    standard-fact axiom candidates (pullback iso of Ω¹; `dz` has order-2 pole at ∞).
    → human fork (prove vs axiomatize).
- **C2 — dropped** (was the RR `h⁰(P)=1` packaging; unnecessary given C1).

### Phase G — assemble G3 + the general theorem
- **G3.** `(Q₁)−(Q₂) ∈ PrincipalDivisors` ⇒ `∃ f, div f = (Q₁)−(Q₂)` (D3) ⇒
  [C1 contrapositive, `genus>0`] `Q₁=Q₂` (else genus 0). No RR needed if C1
  used directly; RR/`h⁰` route is the textbook packaging.
- **G1.** `ofCurveImpl P Q = abelJacobiDiv ((Q : Divisor) − (P))` from the
  `FreeAbelianGroup.lift` defn of `abelJacobiDiv` (finish the `sorry`s in
  `Extensions/AbelJacobi.lean`).
- **G-assemble.** `AX_ofCurve_inj` ⟶ theorem: G1 + `AX_AbelTheorem` + G3. Retire
  the `AX_ofCurve_inj` axiom. (Audit: −1 axiom.)

## Sequencing & forks
S1 → D1→D2→D3 (unblocks the *statement* of G3) → C1 (the hard core) ∥ L1/L2/C2
(RR packaging) → G1 → G-assemble. C1 is the genuine difficulty.

**New-axiom forks (escalate, do not self-authorize):**
- L2 if `H0` de-opaque proves too costly (bridge lemma as axiom).
- C1 if "bijective holomorphic ⇒ biholo" or "genus biholo-invariant" is missing
  from Mathlib/vendor and too large to prove now.
Each such fork PARKS with `blocked: needs human — <the axiom question>`.

## Guardrails
- No relabelling: `AX_ofCurve_inj` and `PrincipalDivisors` must become *derived*,
  not renamed. Every de-opaque must keep `AX_AbelTheorem`/`AX_RiemannRoch`
  statements verbatim.
- Verify each landed piece with `lake build` + kernel `#print axioms` on fresh
  oleans (NO `sorryAx`, NO new axiom beyond escalated+approved forks).
- Disjoint from the in-flight elliptic witness (`OfCurveInj.lean`) — safe to run
  in parallel.

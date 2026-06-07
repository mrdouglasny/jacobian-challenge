> **⚠️ SUPERSEDED — vetting doc, never adopted.** This is a vetting/proposal record for a *new* candidate axiom (`AX_LoopIntegralInLattice` / `AX_Period_Triangle`) considered as a route to retire `AX_ofCurve_inj`. Neither candidate was ever added to the kernel (no such declaration exists), and `AX_ofCurve_inj` was independently DISCHARGED (2026-06-05, Abel injectivity now a theorem). This plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# Vetting request: the `AX_LoopIntegralInLattice` axiom (and a proposed triangle reformulation)

**For external deep-think review.** Self-contained. The goal is to add ONE
low-level, faithful, known-true axiom and DERIVE the high-level injectivity axiom
`AX_ofCurve_inj`, retiring the latter. Please vet the formulation: is it
**faithful, non-vacuous, non-circular, sufficient, and not over-strong**, and
which of the two candidate forms (loop vs triangle) is the cleanest to formalize?

---

## 1. Context (Lean 4 / Mathlib formalization of Buzzard's Jacobian Challenge)

`X` = compact connected complex 1-manifold (Riemann surface), `genus X = g`.
- `HolomorphicOneForm X` — holomorphic 1-forms; `jacobianBasis X : Basis (Fin g) ℂ (…)`.
- `canonicalArcIntegral (γ : AnalyticArc X) (ω) : ℂ` — the line integral `∮_γ ω`, a
  moving-chart `∫₀¹ coeff·deriv`. Defined for piecewise-analytic arcs; if the
  integrand is non-integrable it is `0` by Mathlib's `intervalIntegral` convention.
- `AnalyticLoop X x₀` — a piecewise-analytic loop based at `x₀` (an `AnalyticArc`
  with `extend 0 = extend 1 = x₀`).
- `periodMap X x₀ : H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)` = `loopIntegralToH1`,
  built from a chosen analytic **cycle basis** `cb` of `H1 X x₀` (axiomatized as
  `AX_AnalyticCycleBasis`): on the i-th basis loop it returns `∮` of that loop.
- `periodMapInBasis X x₀ b : H1 X x₀ →ₗ[ℤ] (Fin g → ℂ)` = coordinates of `periodMap`.
- **`periodLatticeInBasis X x₀ b : Submodule ℤ (Fin g → ℂ) := range (periodMapInBasis X x₀ b)`** — the period lattice Λ (the ℤ-span of the cycle-basis periods). `IsZLattice` via `AX_PeriodLattice`.
- `Jacobian X = ULift ((Fin g → ℂ) ⧸ periodLatticeInBasis X (arbitrary) (jacobianBasis X))`.
- `ofCurveAmbient X b Q : Fin g → ℂ`, `i ↦ canonicalArcIntegral (bridgePathArc b Q) (jacobianBasis X i)` — the vector `(∮_{bridgePath(b,Q)} ω_i)_i` over an EXPLICIT chart-by-chart path `bridgePath b Q` from `b` to `Q`.
- `ofCurveImpl X b : X → Jacobian X`, `Q ↦ [ ofCurveAmbient b Q − ofCurveAmbient b b ]` (basepoint-normalized; `ofCurveImpl b b = 0`).

## 2. What is already proven / kept (so the derivation is genuine, not circular)

- **G3 (proven, no extra axiom):** `principal_imp_eq_of_genus_pos : 0 < genus X → ∀ Q₁ Q₂, ((Q₁)−(Q₂)) ∈ PrincipalDivisors X → Q₁ = Q₂`. (Via: a degree-1 map to ℙ¹ forces genus 0, by conservation-of-number; `PrincipalDivisors = range divHom` where `divHom f = Σ orderAt(p,f)·(p)`.)
- **Abel (kept axiom, degree-0 corrected):** `AX_AbelTheorem : (abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker = PrincipalDivisors X`, where `abelJacobiDiv = FreeAbelianGroup.lift (ofCurveImpl X (arbitrary))`.
- **Elliptic instance ALREADY PROVEN (no extra axiom):** `analyticLoop_canonicalArcIntegral_ellipticDz_mem_lattice : ∀ (γ : AnalyticLoop (Elliptic ω₁ ω₂ h) x₀), canonicalArcIntegral γ.arc (ellipticDz) ∈ ellipticLattice` — the genus-1 case of the proposed axiom, proven via the `ℂ/Λ` covering lift. This is strong evidence the general statement is TRUE.

## 3. The axiom we want, and the missing link

The ONLY missing link to derive `AX_ofCurve_inj` for genus>0 is **basepoint-independence of the degree-0 Abel difference**:
> `ofCurveImpl b Q₁ − ofCurveImpl b Q₂` is independent of `b` (in `Jacobian X`).
Given that, `abelJacobiDiv((Q₁)−(Q₂)) = ofCurveImpl(b) Q₁ − ofCurveImpl(b) Q₂`; if `ofCurve b Q₁ = ofCurve b Q₂` then this is 0, so `(Q₁)−(Q₂) ∈ ker ⊓ deg-0 = PrincipalDivisors` (Abel) `⇒ Q₁=Q₂` (G3). Injectivity follows; retire `AX_ofCurve_inj`.

Earlier external review (`gemini-3-pro-preview` deep-think, this project, 2026-05-31) established that basepoint-independence is EQUIVALENT to homotopy invariance of the path integral (not weaker), and recommended isolating exactly this analytic fact as a minimal axiom. We chose to add it after the from-scratch homotopy-invariance proof (a "developing map" construction) got its well-definedness + base case proven but stalled on the bridge + homotopy-cell telescoping.

### Candidate Form A — loop form
```lean
axiom AX_LoopIntegralInLattice (x₀ : X) (γ : AnalyticLoop X x₀) :
    (fun i => canonicalArcIntegral γ.arc (jacobianBasis X i))
      ∈ periodLatticeInBasis X x₀ (jacobianBasis X)
```
Concern (self-audited): faithful, non-vacuous, non-circular, but deriving
basepoint-independence from it needs (i) **arc concatenation/reversal**
infrastructure (to form the cocycle loop `bridge(b,Q)·bridge(b',Q)⁻¹·(b'→b)` and
split its integral additively) — currently MISSING in the repo — and (ii)
identifying `periodLatticeInBasis` across different basepoints `b, b'`.

### Candidate Form B — triangle/cocycle form (proposed by `gemini-3-pro-preview` deep-think, this session)
Fix one global reference basepoint and `Λ := periodLatticeInBasis X x_ref (jacobianBasis X)`. Then:
```lean
axiom AX_Period_Triangle (x y z : X) (p_xy : Path/Arc x y) (p_yz : Arc y z) (p_xz : Arc x z) :
    (fun i => ∮_{p_xz} ω_i) − ((fun i => ∮_{p_xy} ω_i) + (fun i => ∮_{p_yz} ω_i)) ∈ Λ
```
Claim: same mathematical content (the three paths form a 1-cycle `p_xz − p_xy − p_yz`, whose integral ∈ Λ), but **basepoint-independence becomes ~4 lines of mod-Λ algebra** with NO arc-concatenation, NO loop-reversal, NO cross-basepoint lattice identification (apply the triangle to `(b', b, Q₁)` and `(b', b, Q₂)`, subtract; the `b'→b` term cancels). With `x=y` and `p_xx` constant it also gives path-independence of `ofCurve` mod Λ for free.

## 4. Findings so far (to confirm or correct)
- Form A: WELL-FORMED mathematically (faithful homology statement, true, non-circular) but formalization-hostile (needs missing path-algebra).
- Form B: the deep-think recommended REFORMULATE to the triangle form to eliminate the infrastructure burden, same content.

## 5. Questions for your review
1. Is Form A `(∮_γ ω_i)_i ∈ (ℤ-span of cycle-basis periods)` the faithful statement, and is it TRUE on a compact Riemann surface (homology, weaker than homotopy invariance but implied by it)?
2. **Non-circularity:** does either form secretly presuppose `ofCurve` injectivity, or anything about divisors/meromorphic functions? (We believe not — both are purely about closed-1-form integrals landing in a lattice.)
3. **Is Form B genuinely equivalent to Form A** in content, and does it genuinely make basepoint-independence trivial without hidden cost? Any subtlety in the triangle form (e.g. orientation, the choice of paths, the constant-path/well-definedness corollary)?
4. **Vacuity / over-strength:** any way either is vacuously true (e.g. if Λ were the whole space, or `loop` admitted only the constant loop) or FALSE (e.g. does stating it for arbitrary piecewise-analytic — not smooth — paths cause trouble; does non-integrability of the moving-chart integrand, where `canonicalArcIntegral = 0`, create a wrong instance)?
5. **Best formulation:** which form (A, B, or another) is the cleanest faithful axiom that minimizes supporting infrastructure while remaining an honest statement of "loop integrals lie in the period lattice"? If another form is better (e.g. stating it as "`periodMap` is well-defined on all of `H1`, and every loop's class is in the span of the cycle basis"), give the precise statement.
6. Any non-vacuity/soundness landmine we should guard against (cf. a prior axiom in this project, `AX_AbelTheorem`, that was accidentally FALSE before a degree-0 restriction was added).

Please give a crisp verdict (WELL-FORMED / WELL-FORMED-WITH-CAVEAT / REFORMULATE) and, if reformulate, the exact recommended Lean-level statement.

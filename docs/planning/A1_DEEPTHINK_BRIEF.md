# Brief for an external reasoning model — discharging / thinning the torus-uniformization axiom

You are asked to **find the best strategy** to remove (or minimize) the last classical axiom in a
Lean 4 / Mathlib formalization of the Jacobian/Albanese of a compact Riemann surface. Propose a
better strategy if one exists; otherwise stress-test the one below. Be concrete about Lean/Mathlib.

## 1. The mathematical goal

`A` is a **compact, connected, complex Lie group modelled on `ℂ^m`, given as an additive (hence
abelian) Lie group**. In Lean:
```
{m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
  [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
  [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
```
(`ω` = real-analytic/holomorphic smoothness order, standard in this project.) We need:
`A ≅ ℂ^m/Λ` (biholomorphic group iso) for a full `ZLattice Λ ⊂ ℂ^m`, **packaged** as a structure
`TorusSelfAlbanesePresentation m A` whose payload is: the lattice `Λ`; `fromQuot : ℂ^m/Λ → A` (a
holomorphic group iso); `liftCoord : A → ℂ^m` (a section); and the **self-Albanese coordinate
identity** (already corrected to be sound — see §5):
```
liftCoord_eq_albanese : for invariant 1-forms I,I₀ and paths γ:0→a, γ₀:0→0 with
  (∀ ell, I ell = ∫_γ ell) and (∀ ell, I₀ ell = ∫_{γ₀} ell),
  liftCoord a − (coord(I) − coord(I₀)) ∈ Λ
```
Here invariant 1-forms are modelled as **constant covectors**: `TorusHolomorphicOneForm m A :=
Module.Dual ℂ (Fin m → ℂ)` (this modelling — that a translation-invariant holomorphic 1-form on a
complex torus is a constant cover-linear functional — is already a discharged `def`, not an axiom);
`coord(I) := torusAlbaneseCoordinateOfFunctional I` is the ℂ^m-vector dual to `I`; `∫_γ ell :=
torusLineIntegral ell γ = ∫₀¹ ell(γ'(t)) dt` (chart-velocity of the path paired with the constant
covector).

This is classical: Birkenhake–Lange, *Complex Abelian Varieties*, Ch. 1. Because `A` is **given**
abelian, the usual "compact connected complex Lie group ⇒ abelian" maximum-principle step is FREE.

## 2. Context (what is already proved, so you know the surrounding API)

- The 24 curve-side "Buzzard challenge" headlines are axiom-free (standard 3 Lean axioms only).
- Albanese categoricity `ofCurve_isJacobian` (every pointed holomorphic `f : X → A` from the curve
  to a complex torus factors uniquely through the Abel–Jacobi map by a holomorphic group hom) is
  PROVED, currently resting on exactly two axioms: this torus axiom (A1) and a Kirov-interface
  axiom AK (`AX_curve_image_subgroup_isOpen`, local Jacobi inversion — separately scoped, ~25-decl
  port, considered tractable).
- G2/G3/G4 (`torus_self_albanese`, `period_functoriality`, `curve_generates_jacobian`) are theorems
  consuming `TorusSelfAlbanesePresentation`. So A1 only needs to PRODUCE that structure.

## 3. The hard constraint — what Mathlib has and lacks (verified 2026-06-14)

**Mathlib LACKS** (a known frontier): a Lie-group exponential map; global flows / integral curves of
vector fields on manifolds usable for this; complex ODEs at this generality; the universal cover of
a Lie group / manifold as a Lie group; a manifold maximum-modulus principle.

**Mathlib HAS:** `ZLattice`/`IsZLattice` (rank, FG, free, `instIsZLatticeComap`,
`IsZLattice.isCompact_range_of_periodic`); manifold structure on quotients
(`Geometry/Manifold/Instances/Quotient.lean`); the inverse function theorem for `ContMDiff`
(`ContMDiffAt.to_localHomeomorph`-style); covering-space theory (`Topology.Covering`); the
`LieGroup`/`LieAddGroup` classes; analytic (`ω`) smoothness.

**Consequence:** building `exp` from first principles is a months-scale foundational diff-geo
project. A natural shortcut — define `Φ(v) = n·chart⁻¹(v/n)` (n-fold group sum) — is INVALID at
fixed `n`: an arbitrary chart is not a local homomorphism, so the group law carries a bilinear error
`B(v,w)/n` that only vanishes as `n→∞`, i.e. one must take the limit = rebuild `exp`.

## 4. The proposed strategy (axiomatize only `exp`, prove the rest)

**Proposed minimal axiom** (vetted — see §5):
```lean
structure TorusExp (m : ℕ) (A : Type*) [..the instances of §1..] where
  exp          : (Fin m → ℂ) →+ A          -- bundled additive hom (free map_add/map_zero)
  smooth       : ContMDiff 𝓘(ℂ,Fin m→ℂ) 𝓘(ℂ,Fin m→ℂ) ω exp
  mfderiv_zero : mfderiv 𝓘(ℂ,Fin m→ℂ) 𝓘(ℂ,Fin m→ℂ) exp 0 = ContinuousLinearMap.id ℂ (Fin m→ℂ)
axiom AX_torus_exp {m A} [..] : TorusExp m A
```
**Then prove** `def torus_self_albanese : TorusSelfAlbanesePresentation m A` from `AX_torus_exp`:
1. `ker exp` discrete — `mfderiv = id` + smooth ⇒ local diffeo at 0 (IFT) ⇒ `exp` injective near 0
   ⇒ `ker ∩ U = {0}`.
2. `exp` surjective — `range exp` is an open subgroup of connected `A` ⇒ clopen ⇒ `⊤`.
3. `ker exp` a full `ZLattice` — discrete + `A` compact ⇒ cocompact ⇒ `IsZLattice` of rank `2m`.
4. `fromQuot : ℂ^m/ker → A` — descend `exp` (quotient manifold); group iso + holomorphic.
   `liftCoord` := a section of `exp`.
5. **self-Albanese identity** — `exp`-pullback of a constant covector `ell` is the constant covector
   `ell ∘ d(exp)₀ = ell` (uses `mfderiv_zero = id`); FTC along the lifted path gives
   `∫_γ ell = ell(liftCoord a)` mod `ell(Λ)`. (Meatiest step; reuses the project's `torusLineIntegral`.)

End state: `ofCurve_isJacobian` `#print axioms` = std-3 + `AX_torus_exp` + AK. Effort estimate
~1 week (1–4) + ~1 week (5); nothing blocked (unlike a full `exp` build).

## 5. Vetting verdict so far (confirm, refute, or improve)

Adversarial review (Gemini 3.1-pro + author) found NO fatal flaw:
- **Typing clean**: `TangentSpace I x` is defeq to the model space and `mfderiv : E →L E'` (points
  absent from the type), so `mfderiv exp 0 = ContinuousLinearMap.id` is strictly typed.
- **`mfderiv_zero = id` is NECESSARY** (not arbitrary): with invariant forms = standard dual,
  `∫_γ ell = (ell∘d(exp)₀)(liftCoord a)`, which equals `ell(liftCoord a)` iff `d(exp)₀ = id`. The
  `=id` pins the cover coordinate to the dual basis "on the nose." A weaker "local diffeo at 0"
  axiom would push an arbitrary linear twist `d(exp)₀` into step 5.
- **Satisfiable**: `A=ℂ^m/Λ`, `exp=mk`; the quotient chart is the local inverse of `mk` ⇒
  `mfderiv mk 0 = id`. Non-vacuous; `m=0` degenerates correctly.
- **Sufficient**: deduction 1–5 has no gaps; surjectivity/cocompactness are derived, not assumed.

## 6. Questions for you (a better strategy is welcome)

1. **Is `AX_torus_exp` the right minimal boundary**, or is there a *thinner* / more *standard* /
   more *Mathlib-idiomatic* axiom that still suffices? (e.g. a `PartialHomeomorph` at 0 carrying the
   normalization; a one-parameter-subgroup family; a `CoveringMap ℂ^m A` that is a hom.)
2. **Can the axiom be avoided entirely** by a route that uses *only* what Mathlib has? Candidates we
   considered and their blockers: (a) universal cover (`Topology.Covering` exists) — but proving the
   simply-connected complex abelian Lie cover is `ℂ^m` still seems to need `exp`; (b) building `exp`
   via Mathlib's ODE/flow API — blocked by missing global manifold flows; (c) the curve-side period
   lattice we already have — `A` is abstract, not the concrete Jacobian, so it doesn't obviously
   transfer. Is any of these actually viable, or is there a fourth route?
3. **Is the `mfderiv = id` normalization the cleanest way** to bridge the abstract group to the
   coordinate/dual-basis formulation, or is there a coordinate-free packaging of the self-Albanese
   identity that sidesteps the normalization question?
4. **Step 5 (the self-Albanese FTC)**: cleanest Lean route to `exp*(invariant form)=constant` and
   the FTC-along-the-lift, given the form is a constant covector and `exp` is a smooth hom with
   `d(exp)₀=id`? Any Mathlib lemmas that make this short?
5. **Soundness**: any way the proposed axiom (or the swap replacing the current
   `AX_torus_uniformization : TorusSelfAlbanesePresentation`) could be false, too strong, or
   introduce a hidden inconsistency we have not seen?
6. **Trade-off check**: an alternative is the "concrete-tori escape hatch" — restrict the universal
   property to tori *presented* as `ℂ^m/Λ` (carry the presentation as data), making A1 vanish (0
   axioms) at the cost of categoricity only against concrete (not abstract) `A`. Is that a better
   overall design than keeping one minimal `exp` axiom, for a formalization whose headline value is
   the curve-side challenge (already axiom-free)?

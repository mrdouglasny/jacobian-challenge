# Codex adversarial review — Jacobian Challenge formalization plan

Date: 2026-04-20

Sources read in full: `formalization-plan.md:1-731`, `gemini-review.md:1-110`. Pin checked against `lake-manifest.json:4,8,11` and Buzzard's target signatures in `Jacobians/Challenge.lean:57-152`.

## Methodology note

I read the amended plan end-to-end first, then read the Gemini review end-to-end and treated its findings as already claimed. I then checked the pinned local Mathlib tree for the specific API questions raised here, citing concrete files and declarations where I found them. Where I am inferring feasibility rather than reporting a directly present declaration, I mark that as an inference or `HYPOTHESIS`.

## Pushback on the 10 targets

### 1. AddCircle transport for `LieAddGroup`

**Verdict:** LIKELY BROKEN.

Gemini already flagged the real-vs-complex caveat. The stronger pin-specific problem is that `AddCircle` does not appear to have the promised real Lie-group infrastructure at all. Its own file still lists "Lie group structure" under `TODO` (`Mathlib/Topology/Instances/AddCircle/Defs.lean:48-50`). The exposed API I found gives quotient/topological structure (`Mathlib/Topology/Instances/AddCircle/Defs.lean:21-24`), path-connectedness and compactness (`Mathlib/Topology/Instances/AddCircle/Real.lean:29-41`), and a normed additive group (`Mathlib/Analysis/Normed/Group/AddCircle.lean:43`), but no `ChartedSpace`, `IsManifold`, or `LieAddGroup` instances.

That matters because the amended plan makes the transport shortcut primary (`formalization-plan.md:7`, `147-151`, `651-652`). But `LieAddGroup` over a complex model is exactly the class requiring `CMDiff` addition and negation in the chosen manifold structure (`Mathlib/Geometry/Manifold/Algebra/LieGroup.lean:60-67`). So the current issue is not merely "real smoothness does not imply holomorphy"; at the pin, the source `AddCircle` Lie structure needed for the transport is itself missing.

### 2. Chart-cocycle fallback and `fderiv (c₂ ∘ c₁.symm)`

**Verdict:** OK IN PRINCIPLE, UNDER-ESTIMATED.

The fallback cocycle is written in raw chart language:
`coeff c₂ ((c₂ ∘ c₁.symm) z) * D (c₂ ∘ c₁.symm) z = coeff c₁ z` (`formalization-plan.md:284-292`). Mathlib's supported derivative API around charts is not phrased that way. The chart-change infrastructure is built around extended charts and `extendCoordChange` as a `PartialEquiv` into the model vector space (`Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:12-27`, `320-337`), together with `contDiffWithinAt_extendCoordChange` and `isInvertible_fderivWithin_extendCoordChange` on source/target sets (`Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:372-419`).

The bridge `mfderiv = fderiv` exists only once you are already on model spaces (`Mathlib/Geometry/Manifold/MFDeriv/FDeriv.lean:103-117`). Inference: the current cocycle formula is not aligned with the ergonomic API at the pin; you will likely end up rewriting it in terms of `extendCoordChange`, `fderivWithin`, and `range I`, i.e. exactly the plumbing the target question worries about. The amended plan still understates this (`formalization-plan.md:272-299`).

### 3. `pushforward_pullback` infrastructure timing

**Verdict:** THE LONGER ESTIMATE IS CLOSER.

Gemini already called the original estimate unrealistic. The new issue is that the amendment did not really isolate the missing infrastructure. `Functoriality.lean` is now said to "use branch-locus theory" (`formalization-plan.md:666`), `PushPull.lean` is still budgeted at 2 months (`formalization-plan.md:667`), and the plan itself admits branch-locus / fiber-degree / local-multiplicity theory is "essentially greenfield in Mathlib" (`formalization-plan.md:677`).

The nearby Mathlib foothold is only local one-variable meromorphic order/divisor theory on functions `𝕜 → E`, not manifold maps: `meromorphicOrderAt` (`Mathlib/Analysis/Meromorphic/Order.lean:39-50`) and `MeromorphicOn.divisor` (`Mathlib/Analysis/Meromorphic/Divisor.lean:36-41`, `63-69`). That does not give you finiteness of branch locus, constant cardinality of regular fibers, or fiber-sums of holomorphic 1-forms on surfaces.

A further inconsistency: v0.1 still promises an explicit genus-2 hyperelliptic `pushforward_pullback` example (`formalization-plan.md:715`), so this "later" infrastructure is quietly being pulled back into the earlier milestone. Inference: 2 months is not credible unless you axiomatize substantial parts of (a)–(c).

### 4. Universe polymorphism

**Verdict:** PROBABLY A NON-ISSUE.

`LinearMap` is universe-polymorphic with no hidden lift beyond its domain and codomain (`Mathlib/Algebra/Module/LinearMap/Defs.lean:85-87`). `ContMDiffSection` is likewise just a structure over a dependent function `∀ x, V x` (`Mathlib/Geometry/Manifold/VectorBundle/SmoothSection.lean:287-293`). So `JacobianAmbient X := HolomorphicOneForm X →ₗ[ℂ] ℂ` as written in the plan (`formalization-plan.md:414-423`) can plausibly stay in `Type u`.

`HYPOTHESIS:` if `HolomorphicOneForm X` is implemented either as a section of a bundle over `X` or as a chart-cocycle indexed by charts of `X`, and you do not introduce an avoidable universe lift in that packaging, it should remain in `Type u`; then `periodLattice` and the quotient also stay there (`formalization-plan.md:418-423`). I do not see a genuine universe explosion here.

### 5. `genus X := finrank ...` and silent collapse to `0`

**Verdict:** REAL BUG UNLESS `AX_FiniteDimOneForms` IS AN INSTANCE.

There is an internal inconsistency in the amended plan itself. §4.6 first says
`genusAnalytic X := Module.rank ℂ (HolomorphicOneForm X)` with a later cast to `ℕ` (`formalization-plan.md:395-400`). But §5.1 and §7 switch to `Module.finrank` directly (`formalization-plan.md:440`, `573`).

Your worry about silent `0` is therefore not hypothetical. The plan never says whether `AX_FiniteDimOneForms` is installed as a global instance `[FiniteDimensional ℂ (HolomorphicOneForm X)]` or merely available as a theorem (`formalization-plan.md:400`, `562`). If it is only a theorem, then `Module.finrank` can indeed collapse to `0`, and Lean can build a degenerate `ChartedSpace (Fin 0 → ℂ)` while the actual dual space is not 0-dimensional. That is a type-correct failure mode, not a harmless quirk.

### 6. Basis-free Jacobian and `ChartedSpace` coherence

**Verdict:** NON-ISSUE IF CENTRALIZED, COHERENCE RISK IN THE CURRENT DOCUMENT.

A single named `noncomputable instance` using one chosen basis is usually coherent enough: elaboration reuses that constant, it does not independently "choose a new basis every time". So the mere presence of `Basis.ofVectorSpace` is not the real threat.

The actual coherence risk is architectural duplication. §2 still says `Jacobian/Construction.lean` is `Jacobian X := AbelianVariety (τ X)` and that `Jacobian/` is "take `τ(X)` from Part B, feed to Part A" (`formalization-plan.md:57`, `81`). §5.1 then says the type is basis-free and only the instances use a chosen basis (`formalization-plan.md:422-444`). If both stories survive into code, then yes, you can create competing `ChartedSpace` structures on the same `Jacobian X`. Inference: the basis choice itself is manageable; the current document's coexistence of old and new constructions is not.

### 7. Sard-free `ContMDiff.degree`

**Verdict:** ORDER/DIVISOR IS THE LESS-WRONG CHOICE.

The displayed definition still starts with "pick any regular value" (`formalization-plan.md:499-505`). I found no Sard or regular-value theorem at the pin. In fact, the nearest global reference still lists the needed Sard-type result as future work: `WhitneyEmbedding.lean` says the weak Whitney theorem "requires a version of Sard's theorem" and leaves it under `TODO` (`Mathlib/Geometry/Manifold/WhitneyEmbedding.lean:19-24`).

By contrast, Mathlib already has local multiplicity infrastructure in one complex variable: `meromorphicOrderAt` (`Mathlib/Analysis/Meromorphic/Order.lean:39-50`, `92-95`) and divisors (`Mathlib/Analysis/Meromorphic/Divisor.lean:36-41`, `63-69`). So if you insist on a non-axiomatic start, the less-wrong move is to define local degree via order of `f - q` in charts and global degree as a sum of local orders. That is still hard to globalize to manifolds, but it at least starts from existing local API instead of a missing Sard theorem.

### 8. Missed alternative: de Rham + Hodge

**Verdict:** WORSE PATH, NOT CLEANER.

The plan itself already quarantines the Hodge-theoretic identity
`dim H¹_dR = 2 · dim H⁰(Ω¹)` as later work, not critical-path work (`formalization-plan.md:402`). If you redefine the Jacobian via `H¹_dR` + Hodge decomposition, you move exactly that postponed theorem onto the critical path.

The pinned Mathlib state also points the wrong way for this alternative. There are differential forms on normed spaces, not manifolds (`Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean:14-18`, `34-45`, `61-89`). Singular homology exists (`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean:15-18`, `53-56`). But I did not find manifold de Rham cohomology or a Hodge decomposition package. So the de Rham + Hodge route currently adds more greenfield than the period-lattice route.

### 9. Track 2 hyperelliptic `Complex.cpow` branch cuts

**Verdict:** (a) EXPLICIT LIFTED PATHS ARE LEAST PAINFUL.

Option (b), integrating directly on the Riemann surface, drags Track 2 back through the Part B `pathIntegral` machinery that the plan itself marks as the major blocker (`formalization-plan.md:300-321`, `660`). That defeats the point of Track 2.

Option (c), reducing to a real improper integral and patching via the two-sheet atlas, does not actually avoid the branch-choice problem. §3.5.3's claim that the periods are computable by `intervalIntegral` + residues (`formalization-plan.md:220`) still needs a proof that the chosen branch on the slit plane matches the upper/lower sheet lift. So (c) secretly reintroduces explicit path lifting.

The plan's own fallback in §11 points to the right answer: start with explicit real-analytic parameterizations of the lifted cycles as arcs in the upper half-plane avoiding branch points (`formalization-plan.md:697-698`). That is option (a). It is still painful, but it is the least painful.

### 10. Internal consistency of the amended plan

**Verdict:** SEVERAL MISMATCHES; ONE SUBQUESTION IS A NON-ISSUE.

The biggest mismatch is not just the missing `IntersectionForm → Construction` edge. The module list and dependency graph still describe the old `τ`-based architecture:
`Jacobian/Construction.lean (Jacobian X := AbelianVariety (τ X))` (`formalization-plan.md:57`),
"take `τ(X)` from Part B, feed to Part A" (`formalization-plan.md:81`),
and the graph routes `Periods (+ AX_RiemannBilinear)` into `Construction` (`formalization-plan.md:600-602`).
But §5.1 defines `Jacobian X` basis-free as `JacobianAmbient X ⧸ periodLattice X x₀` (`formalization-plan.md:414-423`).
Those cannot both be the architecture.

On the specific subchecks:
- The §8 graph does **not** correctly reflect the amended basis-free architecture. For that architecture, `Construction` should depend directly on `periodMap` plus lattice properties, not on normalized `τ`; and if lattice properties come via period injectivity / rank, then `IntersectionForm` is relevant more directly than the graph suggests (`formalization-plan.md:369-387`, `414-440`, `589-626`).
- The §9 budget **does** include `IntersectionForm.lean` as `B4` (`formalization-plan.md:662`). That part is consistent.
- `AX_RiemannRoch` is **not** fully consistently flagged. §6.1 says the genus-0 theorem follows from `AX_RiemannRoch` plus finite-dimensional one-forms (`formalization-plan.md:550-552`, `572`), but the proof sketch explicitly uses Serre duality (`formalization-plan.md:548`, `550`), and Serre duality is not listed as a separate axiom in §7 (`formalization-plan.md:560-569`).

There is one more cross-section mismatch worth calling out: §4.6 defines analytic genus via `Module.rank ... toNat` (`formalization-plan.md:395-400`), while later sections use `Module.finrank` (`formalization-plan.md:440`, `573`). Sections 4, 5, 7, 8 are not currently speaking the same language.

## Verdict

The amended plan is materially better than the pre-Gemini version, but it still has one hard blocker and several unresolved architectural splits. The hard blocker is the `AddCircle` transport: at the pinned Mathlib state it is not merely "not obviously holomorphic"; it appears not to have the promised source Lie-group API at all. The architectural splits are also real: the document still mixes the old `τ`-based Jacobian story with the new basis-free quotient story, and it uses inconsistent genus definitions. The basis-free core still looks salvageable, but only if the plan is rewritten so that `Construction` really means "quotient by the period lattice", the degree/push-pull stack is either axiomatically fenced off or drastically narrowed, and the hyperelliptic track commits to explicit lifted paths rather than pretending `intervalIntegral` will absorb the branch bookkeeping.

**CRITICAL**

1. The `AddCircle` transport is not just holomorphically suspect; at the pin it lacks the claimed source Lie-group infrastructure, since `AddCircle` still advertises Lie group structure as `TODO` and only exposes topological/normed facts (`formalization-plan.md:147-151`, `651-652`; `Mathlib/Topology/Instances/AddCircle/Defs.lean:48-50`; `Mathlib/Topology/Instances/AddCircle/Real.lean:29-41`; `Mathlib/Analysis/Normed/Group/AddCircle.lean:43`).

2. The document still contains mutually incompatible Jacobian architectures: old `Jacobian X := AbelianVariety (τ X)` in §2/§8 versus basis-free quotient in §5.1 (`formalization-plan.md:57`, `81`, `414-444`, `600-602`).

3. The genus story is internally inconsistent and can silently collapse to `0` unless `AX_FiniteDimOneForms` is installed as an instance before any `finrank`-based definition is used (`formalization-plan.md:395-400`, `440`, `562`, `573`).

**SUBSTANTIVE**

4. The chart-cocycle fallback is written against raw chart compositions, but the actual Mathlib derivative API is built around `extendCoordChange` and `fderivWithin`/`mfderiv`; that plumbing is likely to be a real time sink (`formalization-plan.md:284-292`; `Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:12-27`, `372-419`; `Mathlib/Geometry/Manifold/MFDeriv/FDeriv.lean:103-117`).

5. The revised `pushforward_pullback` schedule still underestimates the missing branch-locus / fiber-holomorphy stack, and v0.1 overpromises by claiming an explicit genus-2 worked example (`formalization-plan.md:666-677`, `715`).

6. The regular-value definition of degree is the wrong lead at this pin; the only serious local foothold is meromorphic order/divisor theory (`formalization-plan.md:499-510`; `Mathlib/Geometry/Manifold/WhitneyEmbedding.lean:19-24`; `Mathlib/Analysis/Meromorphic/Order.lean:39-50`; `Mathlib/Analysis/Meromorphic/Divisor.lean:36-69`).

7. The de Rham + Hodge alternative is not a cleaner fallback in current Mathlib state; it would move a theorem the plan currently postpones (`formalization-plan.md:402`) directly onto the critical path.

**MINOR**

8. Basis choice for `ChartedSpace` is manageable if centralized, but the document should explicitly forbid parallel alternative Jacobian manifold structures (`formalization-plan.md:440-444` together with `57`, `81`).

9. The hyperelliptic implementation story should explicitly choose lifted path parameterizations and stop presenting `intervalIntegral + residues` as if it solved sheet choice (`formalization-plan.md:220`, `697-698`).

10. The genus-0 proof sketch quietly uses Serre duality without admitting it in the axiom story (`formalization-plan.md:548`, `550`, `560-569`).

## Concrete plan amendments

- Rewrite §2 and §8 so that `Jacobian/Construction.lean` is **only** the basis-free quotient `JacobianAmbient X ⧸ periodLattice X`; remove leftover `τ(X)`-based descriptions (`formalization-plan.md:57`, `81`, `602`).

- Rewrite §3.3 to drop `AddCircle` transport as the primary proof strategy at this pin. Either mark it blocked on missing upstream `AddCircle` Lie-manifold infrastructure or replace it with a direct local-chart proof of addition/negation on the quotient (`formalization-plan.md:147-151`).

- Rewrite the §4.1 cocycle fallback using `extendCoordChange` and `fderivWithin`/`mfderiv`, not raw `c₂ ∘ c₁.symm` derivatives (`formalization-plan.md:284-292`; `Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:320-419`).

- Normalize the genus story across §§4, 5, 7: pick one definition, and require `[FiniteDimensional ℂ (HolomorphicOneForm X)]` as an instance before any `genus` or `ChartedSpace` declaration. Do not mix `Module.rank.toNat` and `Module.finrank` (`formalization-plan.md:395-400`, `440`, `573`).

- Rewrite §5.4 so `ContMDiff.degree` is order/divisor-based from the start, or else explicitly axiomatize degree infrastructure. Do not lead with regular values at the current pin (`formalization-plan.md:499-510`).

- Amend §9 and §12 to remove or defer the v0.1 worked `pushforward_pullback` example unless it is explicitly hyperelliptic-only and built with separate axioms for branch-locus finiteness / fiber multiplicity (`formalization-plan.md:667`, `715`).

- Amend §6.1/§7 either by adding an `AX_SerreDuality` placeholder or by rewriting the genus-0 proof sketch so it genuinely avoids Serre duality (`formalization-plan.md:548`, `550`).

- Amend §3.5.3/§11 to commit to option (a): explicit lifted path parameterizations on slit domains, with `Complex.cpow` out of scope for the first implementation pass (`formalization-plan.md:220`, `697-698`).

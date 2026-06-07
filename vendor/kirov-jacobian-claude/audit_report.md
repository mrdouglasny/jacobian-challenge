# Audit Report: `daouid/jacobian-claude` vs. `mrdouglasny/jacobian-challenge`

*Date: June 7, 2026*  
*Context: Auditing our repository (`daouid/jacobian-claude`, a fork of `rkirov/jacobian-claude`) against the parallel attempt (`mrdouglasny/jacobian-challenge`) following Lean Zulip discussion topic `#Autoformalization > jacobian-challenge` (Message ID: 600873396).*

---

## Executive Summary

The two repositories represent two fundamentally different philosophies and workflows for tackling Kevin Buzzard's **Jacobian Challenge (v0.4)** in Lean 4:

1. **Our Repo (`daouid/jacobian-claude` / `rkirov/jacobian-claude`)** is **constructive and proof-driven**. It uses **0 custom axioms** (restricted to standard Lean core axioms + standard `sorryAx` for unproved results). The unproved mathematical surface is restricted to **4 high-level named classical theorems** (Abel's theorem, Cut surface topology, Riemann-Roch, and sphere genus-0 characterization). It develops massive complex analysis foundations in-repo (Čech cohomology, Dolbeault comparison, Serre pairing, and Mittag-Leffler).
2. **Their Repo (`mrdouglasny/jacobian-challenge`)** is **axiomatic and top-down**. It defines **58 custom axioms** (`axiom AX_*`) representing the missing complex analysis theorems. By assuming these axioms, they completely compile the core challenge API (such as `ofCurve_inj` and `pushforward_pullback`) as sorry-free theorems. They focus heavily on concrete algebraic curve families (Track 2: elliptic, hyperelliptic, and plane curves) and maintain a detailed `ROADMAP.md` to systematically replace the 58 axioms with proofs.

To align with their project (as suggested by Rado Kirov in the Zulip thread), we should bridge our real proofs into their axiom framework, identify where our definitions differ, and align our terminology to make it easier for human mathematicians to review the code.

---

## Architectural Contrast

```mermaid
graph TD
    subgraph Our Repo (daouid/jacobian-claude)
        A1[Lean/Mathlib Core] --> A2[Dolbeault / Čech Sheaf Theory]
        A2 --> A3[Real Proofs: Mittag-Leffler, Serre Pairing, Dbar-Pompeiu]
        A3 --> A4[Gated by 4 Classical Sorries]
        A4 --> A5[Buzzard Challenge Conformance]
    end

    subgraph Their Repo (mrdouglasny/jacobian-challenge)
        B1[Lean/Mathlib Core] --> B2[58 Custom Axioms layer]
        B2 --> B3[Track 2: Elliptic, Hyperelliptic, Plane Curves]
        B2 --> B4[Track 1: Jacobian Torus & Abel-Jacobi Map]
        B3 --> B5[Sorry-Free Challenge Proofs modulo Axioms]
        B4 --> B5
    end
    
    A3 -.->|Bridge & Replace| B2
```

| Dimension | Our Repository (`daouid/jacobian-claude`) | Their Repository (`mrdouglasny/jacobian-challenge`) |
| :--- | :--- | :--- |
| **Axiom Policy** | **0 custom axioms**. Uses standard Lean core (`propext`, `Classical.choice`, `Quot.sound`) + standard `sorryAx`. | **58 custom axioms** representing classical theorems (Riemann-Roch, Serre duality, Abel's theorem, etc.). |
| **Completeness** | Leaves mathematical gaps as explicit `sorry` blocks (modularized into helper lemmas). | Proves challenge goals *sorry-free* by assuming the custom axioms. |
| **Track Coverage** | Focuses on **Track 1 (General Riemann Surfaces)**. | Covers **Track 1** and **Track 2 (Concrete Curve Families)**: Elliptic, Hyperelliptic, and Plane curves. |
| **Analysis Infra** | Deep analytical sheaf machinery (Čech-Dolbeault cohomology, Leray covers, $\bar{\partial}$-globalization). | Minimal analysis infra; uses coordinate-wise algebra and vendors our line integrals and lattice quotients. |
| **Human Vetting** | Steered by LLMs with human-in-the-loop review of definitions. | Guided heavily by a mathematical physicist (Michael Douglas) with structural axiom vetting. |

---

## Key Concept Differences

### 1. Genus of a Riemann Surface
* **Our Repo**: Defines `genus X` in `Jacobians/Genus.lean` as the complex dimension of the space of holomorphic 1-forms on $X$:
  ```lean
  def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
    Module.finrank ℂ (HolomorphicOneForm X)
  ```
  This definition is *unconditional* and compiles without axioms.
* **Their Repo**: Defines `genus` similarly but maps it through their `HolomorphicOneForm` type. They successfully prove `genus ℙ¹ = 0` and `genus Elliptic = 1` axiom-free.

### 2. Jacobian Construction
* **Our Repo**: Constructs `Jacobian X` in `Jacobians/ZLatticeQuotient.lean` as a complex torus by quotienting the dual space of holomorphic 1-forms by the period lattice:
  ```lean
  def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u := ...
  ```
  It handles the universe polymorphism (`Type u`) by defining a custom `ULiftManifold` to lift the complex manifold structure of the torus.
* **Their Repo**: Constructs `Jacobian X` using a coordinate-based model `ComplexTorus (Fin (genus X) → ℂ) (periodLattice X)`. They also provide the category-theoretic **Albanese universal property** `IsJacobian` as a compiling statement in `Jacobians/UniversalProperty.lean`, preparing for categoricity proofs.

### 3. Abel-Jacobi Map and Injectivity
* **Our Repo**: Bridges `ofCurve` to the classical Abel-Jacobi map on divisors. Injectivity (`ofCurve_inj`) is proven *modulo* two standard `sorry`s:
  1. `abelJacobi_twoPoint_ne_zero` (representing Abel's theorem: two-point divisor of degree 0 is principal iff the points are equal).
  2. `exists_cutSurface` (cut-chart topology / period matrix linear independence).
* **Their Repo**: The injectivity proof `ofCurve_inj` is completely sorry-free, discharged directly by assuming the axiom `AX_ofCurve_inj`.

### 4. Holomorphic Map Degree
* **Our Repo**: Defines `ContMDiff.degree f hf` in `Jacobians/ProperMapDegree.lean` using sheet-counting over regular values (using a ported version of B. Sanchez's degree-fibre cardinality proof). This is **100% axiom-clean** and proven.
* **Their Repo**: Defines degree axiomatically or uses a simplified placeholder that is subsequently justified by the axiom `AX_pushforward_pullback`.

---

## Mathlib Version Gap and Compatibility Fixes

During our integration work on `main`, we checked out their `Jacobians/` folder and encountered several critical compilation failures stemming from differences in the pinned Mathlib versions. These have all been successfully repaired in the workspace:

1. **Unknown Identifier `lineMap_mem_segment`**:
   - *Problem*: `BridgePath.lean` uses `lineMap_mem_segment` to prove that a flat line segment segment lies in the convex hull. This lemma exists in newer Mathlibs but is missing in our pinned Mathlib commit (`8e3c989`).
   - *Resolution*: Proved `flatSegment_mem_segment` directly from the definition of convex segment (`Convex.segment`) using the convex coefficients `1 - flatReparam t` and `flatReparam t`.
2. **Missing `Homeomorph.connectedSpace_iff`**:
   - *Problem*: `ProjectiveCurve/Hyperelliptic.lean` tries to project `connectedSpace_iff` from homeomorphisms representing parity equivalence. This lemma is missing in our local Mathlib.
   - *Resolution*: Defined a local equivalence helper `Homeomorph.connectedSpace_iff` using `Surjective.connectedSpace` under `symm.continuous`.
3. **Diamond/Synthesis failure for `IsScalarTower ℝ ℂ ℂ` & `ContinuousSMul ℝ ℂ`**:
   - *Problem*: Composing real and complex derivatives or using restrictScalars fails because Lean fails to synthesize these instances in `RiemannSurface/IntegrandIndependence.lean`, `Bridge/BridgePathArc.lean`, and `RiemannSurface/DevelopingBridge.lean`.
   - *Resolution*: Explicitly passed `instIsScalarTower_R_C_C` where needed, imported `Mathlib.Analysis.Normed.Module.Basic`, and set `set_option backward.isDefEq.respectTransparency false` to bypass defeq checks.
4. **Universe Level Mismatch in `connectedSpace_iff`**:
   - *Problem*: In `Jacobians/Jacobian/Construction.lean`, defining `Homeomorph.connectedSpace_iff` with implicit type parameters and helper functions introduced universe level mismatches under asynchronous compilation.
   - *Resolution*: Defined `_root_.Homeomorph.connectedSpace_iff_local` as a `_root_` lemma with a universe-safe direct proof.
5. **Unknown constant `convexComb`**:
   - *Problem*: `HomotopyInvarianceDevelop.lean` referenced `convexComb`, which is named `convexCombo` in our pinned Mathlib.
   - *Resolution*: Renamed all 11 occurrences to `convexCombo` (plus lemma variants `le_convexCombo` / `convexCombo_le`).
6. **Missing universe variables `u`, `v`, `w`**:
   - *Problem*: `AbelJacobiMap.lean`, `AbelTheorem.lean`, `OfCurveInjective.lean`, and `TorusAlbanese.lean` used universe letters in explicit type binders (e.g. `{X : Type u}`) without declaring them via a `universe` command, causing compilation errors.
   - *Resolution*: Added `universe u v w` (or `universe u`) at the top of these files.

---

## Triage of Their 58 Axioms vs. Our Proofs

Their repository uses 58 axioms to bridge missing Mathlib/Lean features. Many of these axioms correspond directly to things we have either **proved** or **isolated to specific sorries**:

| Their Axiom Name | Their File | Our Status / Correspondence |
| :--- | :--- | :--- |
| `AX_FiniteDimOneForms` | `Bridge/KirovHolomorphic.lean` | **Proved.** We proved the finite dimensionality of the space of holomorphic 1-forms in `Montel.lean` using per-chart compact-analytic families. |
| `AX_IntersectionForm_perfect` | `Axioms/IntersectionForm.lean` | **Isolated.** Part of our `exists_cutSurface` sorry in `CutSurfaceRelations.lean` which establishes the intersection form on $H_1(X, \mathbb{Z})$. |
| `AX_RiemannRoch` | `Axioms/RiemannRoch.lean` | **Isolated.** Corresponds to `exists_riemannRoch_divisor` in our `RiemannRoch.lean`. |
| `AX_SerreDuality` | `Axioms/SerreDuality.lean` | **Isolated/In-Progress.** We have structured the Serre pairing surjectivity/injectivity proofs in `SerreDualityPairing.lean`, leaving only the 1-form residue integration open. |
| `AX_PeriodLattice` | `Axioms/PeriodLattice.lean` | **Proved/Isolated.** We prove the discrete lattice structure in `PeriodLattice.lean` modulo the cut-chart homology basis. |
| `AX_genus_eq_zero_iff_homeo` | `Axioms/Uniformization0.lean` | **Isolated.** Matches our `genus_zero_of_nonempty_homeo_sphere` sorry (backward direction) and Riemann-Roch reduction (forward direction). |
| `AX_ofCurve_contMDiff` | `Axioms/AbelJacobiMap.lean` | **Isolated.** Corresponds to the coordinate chart map holomorphicity, which we prove in `OfCurveAnalyticitySkeleton.lean` modulo period lattice topology. |
| `AX_pushforward_pullback` | `Axioms/AbelJacobiMap.lean` | **Proved/Isolated.** Our `pushforward_pullback` in `ZLatticeQuotient.lean` is proven modulo the period matrix integrals. |

---

## Alignment Opportunities

As discussed on Zulip, the main barrier to collaboration is that our repository uses different type encodings (e.g., our `HolomorphicOneForm` vs. their `HolomorphicOneForm`). 

We can align the repositories through these steps:

1. **Unify Holomorphic 1-Form Encodings**:
   - Our repo defines forms as sections of the cotangent bundle.
   - Their repo uses a coordinate-based or sheaf-cochain-based wrapper.
   - Proving an equivalence (`Equiv`) between these two definitions will allow us to immediately discharge their axioms `AX_FiniteDimOneForms` and `ambientPhi_ambientPsi_eq` using our proven theorems.
2. **Bridge the Line Integral / Path Connexity**:
   - Their repo defines `bridgePath` to show a connected complex manifold is smoothly path-connected, which is needed to define path integrals.
   - We have developed robust line integrals on manifolds in `LineIntegral.lean` and `SmoothPath.lean`.
   - We can replace their `bridgePath` axioms/stubs with our fully proven smooth path concatenation and integration theorems.
3. **Discharge the Algebra-Geometry Axioms**:
   - We can import their algebraic curves definitions (Track 2: `Hyperelliptic.lean` and `PlaneCurve.lean`) into our repo to verify that our Riemann-Roch and Abel-Jacobi machinery works on concrete curves.
   - We can export our `degDiv_eq_zero` and `degree` proofs to discharge their degree-related axioms.

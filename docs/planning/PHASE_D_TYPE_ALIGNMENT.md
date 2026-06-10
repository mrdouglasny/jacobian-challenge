# Phase D — A4 statement-layer type-alignment dossier

*2026-06-10. Complete statement-layer inventory of every definition transitively
mentioned by the two port results we consume —
`Jacobians.Dolbeault.exists_cechModel`
(`vendor/kirov-dolbeault-port/KirovDolbeault/Dolbeault/CechFinitenessWiring.lean:53`) and
`Jacobians.Dolbeault.exists_skyscraperLES`
(`vendor/kirov-dolbeault-port/KirovDolbeault/Dolbeault/CohomologicalRR.lean:156`) —
matched against our axiom layer (`Jacobians/Layer3/Cohomology.lean`).
Companion to `docs/planning/PHASE_D_BRIDGE_PLAN.md`. Paths below are repo-relative;
port paths are relative to `vendor/kirov-dolbeault-port/`.*

## Executive verdict (read this first)

**No blocker-grade mismatch found.** The two feared blockers are both absent:

1. **Cover existence is PROVEN in the port.** `exists_realizableLerayCover`
   (`KirovDolbeault/Dolbeault/SkyscraperProductWitness.lean:246`) produces a
   `FiniteCover X` that is simultaneously `IsLeray` and `LocallyRealizable`,
   witnessed by the *canonical, named* `chartDiskCover`
   (`KirovDolbeault/Dolbeault/LerayCoverExists.lean:212`) with
   `locallyRealizable_chartDiskCover` (`SkyscraperProductWitness.lean:236`).
   So `exists_skyscraperLES`'s `hR : 𝔘.LocallyRealizable` hypothesis is
   dischargeable for a concrete cover, and — better — the finiteness node
   `finiteDimensional_cechH1_wired` (`CechFinitenessWiring.lean:85`) needs **no
   cover hypothesis at all** (any `FiniteCover`, any `Divisor`).
2. **No smoothness-class mismatch.** The port's variable context uses
   `[IsManifold 𝓘(ℂ) ω X]`; ours uses `[IsManifold 𝓘(ℂ) ⊤ X]`. These are the
   *same term*: `ω` is Mathlib's scoped notation for `(⊤ : WithTop ℕ∞)`
   (`Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:117`,
   `scoped[ContDiff] notation3 "ω" => (⊤ : WithTop ℕ∞)`). Both sides demand an
   ANALYTIC manifold; instance resolution is identical.

The substantive bridge work is concentrated in exactly one place: the
**L(D) bridge** — our `riemannRochSpace D ⊆ MeroField X` (quotient-then-submodule)
vs the port's `linearSystem D ⧸ germZeroSubmodule` (submodule-then-quotient) and
its onward identification with Čech `H⁰` (which the port already proves as
`globalSectionsEquivQuot` / `h0Dim_eq_lDim`, `KirovDolbeault/Dolbeault/CechH0.lean:612/619`).

**Sorry hygiene.** The port's sorries live in 4 files: `Abel.lean`,
`CutSurfaceRelations.lean`, `DegreeOneSphere.lean`,
`Dolbeault/SerreDualityPairing.lean`. `Abel.lean` is in the *import* closure of
both targets (it defines `Divisor`), but the two target theorems are
`#print axioms`-clean at standard-3 per the Phase-D plan. Every bridge file MUST
re-run `#print axioms` on its own headline to confirm no `sorryAx` leaks in.

---

## Part 1 — Port side

Common variable context for every port declaration below (universe-polymorphic,
`X : Type*`):

```lean
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```

i.e. a compact connected Hausdorff **analytic** (`ω`) Riemann surface modelled on
`ℂ`. (Exception: `Divisor` itself is declared in `Abel.lean` whose section also
carries `[Nonempty X]`, but the abbreviation mentions only `X`, so `Divisor X`
elaborates without any instances.)

### 1.1 `Divisor` (port) — `KirovDolbeault/Abel.lean:67`

```lean
abbrev Divisor : Type _ := X →₀ ℤ

def Divisor.deg : Divisor X →+ ℤ := Finsupp.degree          -- Abel.lean:71
```

Reading: a divisor is a finitely supported function `X →₀ ℤ`; degree is the sum
of coefficients. Subtlety: it is an `abbrev`, so `Finsupp` API (`Finsupp.single`,
`Finsupp.induction`, `Finsupp.add_apply`) applies transparently — the χ-induction
in `CohomologicalRR.lean` leans on this directly (`D + Finsupp.single P 1`,
`Finsupp.induction`).

### 1.2 `FiniteFamily` / `FiniteCover` — `KirovDolbeault/Dolbeault/CechComplex.lean:35/44`

```lean
structure FiniteFamily (X : Type*) [TopologicalSpace X] where
  ι : Type
  [fintype : Fintype ι]
  U : ι → Opens X

structure FiniteCover (X : Type*) [TopologicalSpace X] extends FiniteFamily X where
  covers : ⨆ i, U i = ⊤
```

Reading: a finite indexed family of opens; a cover additionally exhausts `X`.
Subtleties: (a) **`ι : Type` is fixed at universe 0** — fine for the canonical
`chartDiskCover` (`ι := Fin (chartDiskCenters.card)`), and harmless to us since
our `H1coh` only needs *one* cover; (b) the Čech complex is defined on
`FiniteFamily` (no covering condition) so disk-acyclicity statements are
non-vacuous; `FiniteCover` adds `covers` only where globality matters
(`h0Dim_eq_lDim`, skyscraper apex vertex).

### 1.3 The cochain value type: `MGerm` + `OmegaD` + `OmegaDGerm` — `KirovDolbeault/Dolbeault/CechSection.lean:189/78/240`

This is the sections/germ type the cochains take values in.

```lean
/-- order of a bare function on ↥U, read in U's own chart (CechSection.lean:36) -/
noncomputable def ordU {U : Opens X} (f : U → ℂ) (x : U) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)

/-- Sections of 𝒪_D over U, as raw functions (CechSection.lean:78) -/
noncomputable def OmegaD (D : Divisor X) (U : Opens X) : Submodule ℂ (U → ℂ) where
  carrier := {f | IsMeromorphic (U : Type _) f ∧ ∀ x : U, (-(D x.1) : WithTop ℤ) ≤ ordU f x}
  ...

/-- Germ-class functions on ↥U (CechSection.lean:189) -/
abbrev MGerm (U : Opens X) : Type _ :=
  Filter.Germ (Filter.codiscreteWithin (Set.univ : Set U)) ℂ

/-- 𝒪_D-sections as germ-classes (CechSection.lean:240) -/
noncomputable def OmegaDGerm (D : Divisor X) (U : Opens X) : Submodule ℂ (MGerm U) :=
  Submodule.map (toGerm U) (OmegaD D U)
```

Reading: a cochain entry on an open `U` is a **germ-class** — a function
`↥U → ℂ` modulo agreement off a discrete set (`codiscreteWithin`-equality, i.e.
Mathlib's meromorphic-normal-form junk quotient, realised via `Filter.Germ`).
`OmegaD D U` is Forster's `𝒪_D(U)`: meromorphic on the open submanifold `↥U`
with `ord_x ≥ −D(x)` at every point, where the order is computed in `↥U`'s *own*
subtype chart (Mathlib's automatic `ChartedSpace ℂ ↥U`). `OmegaDGerm` pushes
this submodule into the germ quotient — junk-free with **no manual quotient**.

Soundness subtleties:
- The junk quotient is essential: point-indicator "spikes" are nonzero raw
  functions of order `⊤` everywhere, lie in every `OmegaD D U`, and are linearly
  independent — without the quotient every `h⁰` would be `finrank = 0` (Mathlib
  junk value) and RR would be *false*. The port quotients (germ classes); we
  quotient (our `MeroField`). Both sides made the same design decision.
- `IsMeromorphic` here is the port's manifold-level predicate
  (`Abel.lean:51`: meromorphy of the chart pullback at every point), applied to
  the subtype `↥U`; meromorphy and `ordU` restrict correctly along
  `V ≤ U` because both subtype charts are `subtypeRestr`s of the same ambient
  chart (`restrict_chart_aux`, `ordU_comp_openIncl` — proven).

### 1.4 The Čech complex and `cechH1` / `h0Dim` / `h1Dim` — `KirovDolbeault/Dolbeault/CechComplex.lean:104–181`

```lean
abbrev Cochain0 : Type _ := Π i, MGerm (𝔘.U i)                                  -- :104
abbrev Cochain1 : Type _ := Π p : 𝔘.ι × 𝔘.ι, MGerm (𝔘.U p.1 ⊓ 𝔘.U p.2)          -- :107

noncomputable def cechDelta0 : 𝔘.Cochain0 →ₗ[ℂ] 𝔘.Cochain1 := ...               -- :119
noncomputable def cechDelta1 : 𝔘.Cochain1 →ₗ[ℂ] 𝔘.Cochain2 := ...               -- :125

def sections0 : Submodule ℂ 𝔘.Cochain0 :=        -- {f | ∀ i, f i ∈ OmegaDGerm D (𝔘.U i)}  :145
def sections1 : Submodule ℂ 𝔘.Cochain1 := ...                                   -- :152
noncomputable def cocycles1 : Submodule ℂ 𝔘.Cochain1 :=
  LinearMap.ker 𝔘.cechDelta1 ⊓ 𝔘.sections1 D                                    -- :159
noncomputable def coboundaries1 : Submodule ℂ 𝔘.Cochain1 :=
  Submodule.map 𝔘.cechDelta0 (𝔘.sections0 D)                                    -- :163

abbrev cechH1 : Type _ :=
  ↥(𝔘.cocycles1 D) ⧸ (𝔘.coboundaries1 D).submoduleOf (𝔘.cocycles1 D)            -- :169

noncomputable def globalSections : Submodule ℂ 𝔘.Cochain0 :=
  LinearMap.ker 𝔘.cechDelta0 ⊓ 𝔘.sections0 D                                    -- :174

noncomputable def h0Dim : ℕ := Module.finrank ℂ ↥(𝔘.globalSections D)           -- :178
noncomputable def h1Dim : ℕ := Module.finrank ℂ (𝔘.cechH1 D)                    -- :181
```

(All in namespace `FiniteFamily`; `FiniteCover` inherits via `toFiniteFamily`.
`chi 𝔘 D := (h0Dim : ℤ) − h1Dim` is `CohomologicalRR.lean:98`.)

Reading: the genuine alternating Čech complex on germ-class cochains
(`δ⁰f_{ij} = f_j|_{ij} − f_i|_{ij}`, `δ¹g_{ijk} = g_{jk} − g_{ik} + g_{ij}`),
with the `𝒪_D` sheaf condition carried as a submodule of the *raw* (diamond-free)
function-Pi rather than baked into the cochain type. `cechH1 = Z¹/B¹` is the
honest germ-class `H¹(𝔘, 𝒪_D)`; `globalSections = ker δ⁰ ∩ sections` is `H⁰`
(junk-free, **no quotient needed** — `MGerm` already quotiented).

Universe note: for `X : Type u`, `MGerm U : Type u`, `Cochain1 : Type u`
(`ι : Type 0` index), so **`cechH1 D : Type u` — exactly the universe our
`axiom H1coh (D : Divisor X) : Type u` demands.** No `ULift` needed for the
def-replacement.

Subtlety (cochain encoding): cochains are full products over `ι × ι` (no
ordering/alternation condition on the index, diagonal included) — standard, and
all of the port's downstream machinery is internally consistent with it. Since
we adopt `cechH1` wholesale as an opaque definition, the encoding never leaks
into our layer.

### 1.5 `DiskOverlapData` — `KirovDolbeault/Dolbeault/CechModelBase.lean:61`

```lean
structure DiskOverlapData where
  J : Type
  [fintypeJ : Fintype J]
  [decEqJ : DecidableEq J]
  Uov : J → Set ℂ
  hUov : ∀ p, IsOpen (Uov p)
  Kov : J → Set ℂ
  hKcpt : ∀ p, IsCompact (Kov p)
  hKU : ∀ p, Kov p ⊆ Uov p
```

Reading: the *geometric* skeleton of a sup-norm Čech model — a finite overlap
index `J`, the chart-image of each overlap as an open `Uov p ⊆ ℂ`, and a
relatively-compact shrinking `Kov p ⋐ Uov p`. Cover 1-cochains live in
`Ccov := Π p, BddHol (Uov p)` (bounded-holomorphic Banach), shrinking 1-cochains
in `Cshr := Π p, (Kov p →ᵇ ℂ)`. The restriction `rhoRaw : Ccov →L[ℂ] Cshr`
is a **compact operator** (`rhoRaw_compact`, the Montel payoff — proven).
Note: `DiskOverlapData` mentions no `X`, no cover, no divisor — it is pure
planar data; the tie to `(𝔘, D)` happens only through the existential in
`exists_cechModel` (see soundness note below).

### 1.6 `Coboundaries` and `supH1` — `KirovDolbeault/Dolbeault/CechModelBase.lean:137/222`

```lean
structure Coboundaries (d : DiskOverlapData) where
  C0 : Type
  [ng0 : NormedAddCommGroup C0] [ns0 : NormedSpace ℂ C0] [cs0 : CompleteSpace C0]
  C2 : Type
  [ng2 : NormedAddCommGroup C2] [ns2 : NormedSpace ℂ C2]
  C2cov : Type
  [ng2c : NormedAddCommGroup C2cov] [ns2c : NormedSpace ℂ C2cov]
  δ0 : C0 →L[ℂ] d.Cshr
  δ1 : d.Cshr →L[ℂ] C2
  δ1cov : d.Ccov →L[ℂ] C2cov
  hδδ : δ1.comp δ0 = 0
  hcomm : ∀ x : d.Ccov, δ1cov x = 0 → δ1 (d.rhoRaw x) = 0
  leray : ∀ s : d.Cshr, δ1 s = 0 →
    ∃ (η : C0) (x : d.Ccov), δ1cov x = 0 ∧ s = δ0 η + d.rhoRaw x

-- in namespace Coboundaries, c : Coboundaries d:
abbrev supH1 : Type := c.Z1shr ⧸ LinearMap.range c.δ.toLinearMap   -- :222
-- where Z1shr := ker δ1, δ := δ0 corestricted to Z1shr
```

Reading: the analytic completion of a `DiskOverlapData` to a Čech `δ`-complex in
sup-norm: shrinking-side `δ⁰/δ¹` with `δ¹δ⁰ = 0`, a cover-side `δ¹` whose kernel
is `Z¹(cover)`, the restriction-commutes square, and — the load-bearing field —
**`leray`**, the disk-acyclicity witness: every shrinking 1-cocycle is a
shrinking-coboundary plus the restriction of a cover 1-cocycle. `supH1` is
`Z¹(shrinking)/B¹`. `finiteDimensional_supH1` (`CechModelBase.lean:227`) makes
`supH1` finite-dimensional from Leray surjectivity + compactness of `ρ`
(Forster 14.9 / the standard `L. Schwartz` argument).

Soundness subtlety (KEY DESIGN POINT, `CechModelBase.lean:35–40`): Leray
surjectivity `(η,ξ) ↦ δη + ρξ` is **FALSE** for arbitrary abstract `(δ, ρ)` — a
compact `ρ` cannot surject onto an infinite-dimensional cocycle space. The
`leray` field is precisely what makes `Coboundaries d` mean "a genuine acyclic
chart-disk Leray model", and the honest analytic obligation is concentrated
where models are *constructed* (`exists_cechModel_general`, proven).

### 1.7 Target 1: `exists_cechModel` — `KirovDolbeault/Dolbeault/CechFinitenessWiring.lean:53`

```lean
theorem exists_cechModel (𝔘 : FiniteCover X) (D : Divisor X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d), Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  exists_cechModel_general 𝔘 D
```

plus the corollary we actually consume:

```lean
theorem finiteDimensional_cechH1_wired (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D)                       -- CechFinitenessWiring.lean:85
```

Reading: every finite cover and divisor admit a sup-norm Leray model whose
`supH1` is `ℂ`-linearly isomorphic to the genuine germ-class `cechH1 D`; since
`supH1` is finite-dimensional (Montel + Leray), so is `cechH1 D`. **No
hypotheses on `𝔘` whatsoever** (no Leray, no realizability) — the general-`D`
case climbs from `D = 0` through the skyscraper reduction
(`CechFinitenessDtwist.exists_cechModel_general`, `CechFinitenessDtwist.lean:429`).

**SOUNDNESS NOTE (verbatim concern from `CechFinitenessWiring.lean:57–66`):**
the comparison is *bundled into the existential* — `∃ d c, Nonempty (cechH1 ≃ₗ supH1)` —
rather than stated as a free-`c` equivalence `(𝔘 D d c) → cechH1 D ≃ₗ c.supH1`.
The free-`c` form is FALSE (`supH1` depends only on the model, `cechH1` only on
`(𝔘, D)`; an unrelated acyclic model against a high-genus `(𝔘,D)` has the wrong
dimension). Consequence for us: a bridge may only *destructure* the existential
(`obtain ⟨d, c, ⟨e⟩⟩ := exists_cechModel 𝔘 D`) — never apply a comparison to an
independently chosen model. Since we only consume the `FiniteDimensional`
corollary, this footgun does not reach our layer.

### 1.8 `FiniteCover.LocallyRealizable` — `KirovDolbeault/Dolbeault/SkyscraperConeRealization.lean:99`

```lean
def FiniteCover.LocallyRealizable (𝔘 : FiniteCover X) : Prop :=
  ∀ (D : Divisor X) (P : X) (j : 𝔘.ι) (hP : P ∈ 𝔘.U j),
    Function.Surjective (coeffGermLin hP (D := D))
```

where `coeffGermLin hP : OmegaDGerm (D + Finsupp.single P 1) W →ₗ[ℂ] ℂ`
(`LocalRealization.lean:491`) reads the order-`(−D(P)−1)` Laurent coefficient of
a germ at `P` in `W`'s chart (`coeffWFn`/`laurentCoeff`, defined as the
punctured-limit of the de-poled function; junk `0` off the meromorphic locus).

Reading: **local Mittag–Leffler** — on every cover set containing `P`, every
prescribed top Laurent coefficient is realised by some `𝒪_{D+P}`-germ. This is
the single analytic input of the skyscraper construction.

**Existence is proven, not assumed:**

```lean
theorem locallyRealizable_chartDiskCover :
    (chartDiskCover (X := X)).toFiniteCover.LocallyRealizable    -- SkyscraperProductWitness.lean:236

theorem exists_realizableLerayCover :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable        -- SkyscraperProductWitness.lean:246
```

The witness is the canonical `chartDiskCover` (`LerayCoverExists.lean:212`): a
finite subcover of half-radius chart-disk neighbourhoods extracted by
compactness (`ι := Fin (chartDiskCenters.card)` — universe-0, fine);
realizability comes from the explicit factorized-rational product witness
`∏ᶠ (· − u)^{dz u}` pulled back through the chart
(`exists_orderExact_witness_chartDisk`). Subtlety: the witness has *exact* order
`−D(x)` at every point of the disk — strictly stronger than needed; no vacuity
risk.

### 1.9 `Skyscraper`, `h0Incl`, `h1Map` — `KirovDolbeault/Dolbeault/SkyscraperLESBase.lean:95/78/122`

```lean
abbrev Skyscraper (_𝔘 : FiniteCover X) (_D : Divisor X) (_P : X) : Type := ℂ

noncomputable def h0Incl (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    ↥(𝔘.globalSections D) →ₗ[ℂ] ↥(𝔘.globalSections (D + Finsupp.single P 1)) :=
  Submodule.inclusion (𝔘.globalSections_le_add_single D P)
-- h0Incl_injective : Function.Injective (𝔘.h0Incl D P)            -- :82

noncomputable def h1Map (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.cechH1 D →ₗ[ℂ] 𝔘.cechH1 (D + Finsupp.single P 1) := by
  refine Submodule.mapQ _ _ (𝔘.cocyclesIncl D P) ?_ ; ...
```

Reading: `Skyscraper` is the genuine 1-dimensional stalk `ℂ_P`, *literally `ℂ`*
(arguments are discards — `finrank = 1` is `Module.finrank_self ℂ`, trivially).
`h0Incl` (`f₁`) is the order-weakening inclusion `H⁰(𝒪_D) ↪ H⁰(𝒪_{D+P})`,
injective; `h1Map` (`f₄`) is the same inclusion at the cocycle level, descended
to `H¹` quotients. Both proven, no analytic content.

**Soundness subtlety (the 2026-06-02 fix, docstring at `SkyscraperLESBase.lean:89`):**
the previous `Skyscraper` was the H⁰-cokernel `H⁰(𝒪_{D+P}) ⧸ range f₁` with a
`skyDim : finrank = 1` field — **provably false** at base points of `|D+P|`
(where the cokernel is 0). The fixed design makes the middle term the genuine
`ℂ_P` and demotes the coefficient arrow `f₂ = h0ToSky` (NOT surjective in
general; its image is the cokernel) to honest data inside `SkyscraperLES`. Our
own `cohomologyLES` axiom made the same design choice (`SkyscraperFiber = ULift ℂ`
always 1-dim, `principalPart` not required surjective) — the two structures are
*architecturally aligned*, which is what makes the bridge routine.

### 1.10 `SkyscraperLES` — `KirovDolbeault/Dolbeault/SkyscraperLESBase.lean:168`

```lean
structure SkyscraperLES (𝔘 : FiniteCover X) (D : Divisor X) (P : X) where
  h0ToSky : ↥(𝔘.globalSections (D + Finsupp.single P 1)) →ₗ[ℂ] 𝔘.Skyscraper D P
  exact₁₂ : Function.Exact (𝔘.h0Incl D P) h0ToSky
  f₃ : 𝔘.Skyscraper D P →ₗ[ℂ] 𝔘.cechH1 D
  exact₂ : Function.Exact h0ToSky f₃
  exact₃ : Function.Exact f₃ (𝔘.h1Map D P)
  surj₄ : Function.Surjective (𝔘.h1Map D P)
  [finH1D : FiniteDimensional ℂ (𝔘.cechH1 D)]
  [finH1DP : FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1))]
  [finH0DP : FiniteDimensional ℂ ↥(𝔘.globalSections (D + Finsupp.single P 1))]
```

Reading: the six-term LES
`0 → H⁰(𝒪_D) →[h0Incl] H⁰(𝒪_{D+P}) →[h0ToSky] ℂ_P →[f₃] H¹(𝒪_D) →[h1Map] H¹(𝒪_{D+P}) → 0`
with `f₁` injectivity and `f₄` surjectivity supplied externally
(`h0Incl_injective` proven; `surj₄` a field), plus the three finiteness
instances (all now unconditional theorems in the port). `finH0D` is *derived*
(injects along `h0Incl`).

### 1.11 Target 2: `exists_skyscraperLES` — `KirovDolbeault/Dolbeault/CohomologicalRR.lean:156`

```lean
theorem exists_skyscraperLES (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (D : Divisor X) (P : X) :
    Nonempty (SkyscraperLES 𝔘 D P) :=
  (exists_localRealizationData 𝔘 hR D P).elim fun L => ⟨skyscraperLES_of_localRealization L⟩
```

Reading: for any locally realizable cover, the skyscraper LES exists at every
`(D, P)`. A *theorem* (the snake assembly + star-of-`P` cone construction), with
the single hypothesis `hR` — discharged for `chartDiskCover` by §1.8. Consumed
downstream by `chi_jump_of_LES` (`CohomologicalRR.lean:118`, pure rank–nullity)
and `cohomological_riemannRoch` (`CohomologicalRR.lean:216`):

```lean
theorem cohomological_riemannRoch (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable) (D : Divisor X) :
    (𝔘.h0Dim D : ℤ) - 𝔘.h1Dim D = Divisor.deg X D + 1 - 𝔘.h1Dim 0
```

### 1.12 `FiniteCover.chi` — `KirovDolbeault/Dolbeault/CohomologicalRR.lean:98`

```lean
noncomputable def chi (𝔘 : FiniteCover X) (D : Divisor X) : ℤ :=
  (𝔘.h0Dim D : ℤ) - 𝔘.h1Dim D
```

Euler characteristic; bookkeeping only.

### 1.13 The port's global L(D): `linearSystem` / `germZeroSubmodule` / `lDim` and the `H⁰` bridge

`KirovDolbeault/LinearSystem.lean:232/252(germZero)/269(lDim)`,
`KirovDolbeault/Dolbeault/CechH0.lean:612/619`:

```lean
noncomputable def linearSystem (D : Divisor X) : Submodule ℂ (MeromorphicFunction X) where
  carrier := {f | ∀ x, (-(D x) : WithTop ℤ) ≤ f.orderW x}
  ...

noncomputable def germZeroSubmodule : Submodule ℂ (MeromorphicFunction X) where
  carrier := {f | ∀ x, f.orderW x = ⊤}
  ...

noncomputable def lDim (D : Divisor X) : ℕ :=
  Module.finrank ℂ
    (↥(linearSystem D) ⧸ (germZeroSubmodule).submoduleOf (linearSystem D))

noncomputable def globalSectionsEquivQuot :
    (linearSystem D ⧸ germZeroSubmodule.submoduleOf (linearSystem D))
      ≃ₗ[ℂ] ↥(𝔘.globalSections D)                                   -- CechH0.lean:612

theorem h0Dim_eq_lDim (D : Divisor X) : 𝔘.h0Dim D = lDim D          -- CechH0.lean:619
```

with `MeromorphicFunction X` a structure `(toFun : X → ℂ, meromorphic : IsMeromorphic X toFun)`
(`Abel.lean:55`) and
`orderW f x := meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)`
(`LinearSystem.lean:135`). Reading: the port already proves that Čech `H⁰`
equals the global linear system modulo germ-zero junk (restriction map +
first-isomorphism theorem + a sheaf-gluing surjectivity argument). **This is the
single most valuable pre-built bridge asset**: our L(D)-bridge composes with it
instead of re-fighting the Čech side.

---

## Part 2 — Our side

Common variable context (`Jacobians/Layer3/Cohomology.lean:25`):

```lean
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]
```

Identical to the port's modulo `⊤`/`ω` spelling (same term, §Executive verdict)
and the explicit universe annotation.

### 2.1 `Divisor` (ours) — `Jacobians/RiemannSurface/Divisor.lean:28`

```lean
abbrev Divisor (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : Type u := FreeAbelianGroup X

noncomputable def Divisor.deg (X : Type*) [...] : Divisor X →+ ℤ :=
  FreeAbelianGroup.lift (fun _ : X => (1 : ℤ))                       -- :41
```

(namespace `Jacobians.Axioms`). Coefficients via `FreeAbelianGroup.coeff p D`.
Reading: same mathematical object as the port's, encoded as `FreeAbelianGroup X`
instead of `X →₀ ℤ`. Mathlib supplies
`FreeAbelianGroup.equivFinsupp : FreeAbelianGroup X ≃+ (X →₀ ℤ)` with
`coeff = toFinsupp` evaluation, so translation is a fixed `AddEquiv` plus two
compatibility lemmas (`coeff` ↦ `Finsupp` application, `deg` ↦ `Finsupp.degree`).

### 2.2 `MeroField` and `riemannRochSpace` — `Jacobians/RiemannSurface/Cohomology/RiemannRochSpace.lean:155/294`

```lean
def MeroFunctions (X : Type u) [...] : Submodule ℂ (X → ℂ) where
  carrier := { f : X → ℂ | ∀ p : X, MeromorphicAtX f p } ...          -- :117

def GermZero (X : Type u) [...] : Submodule ℂ (MeroFunctions X) where
  carrier := { f | ∀ p : X, orderAt p (f : X → ℂ) = ⊤ } ...           -- :132

abbrev MeroField (X : Type u) [...] : Type u :=
  MeroFunctions X ⧸ GermZero X                                        -- :155

def orderAtField (p : X) : MeroField X → WithTop ℤ :=
  Quotient.lift (fun f : MeroFunctions X => orderAt p (f : X → ℂ)) ... -- :175

def riemannRochSpace (D : Divisor X) : Submodule ℂ (MeroField X) where -- :294
  carrier :=
    { F : MeroField X |
      ∀ p : X,
        ((-(FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)) : ℤ) : WithTop ℤ) ≤
          orderAtField p F }
  ...
```

with the Wallace primitives
(`Jacobians/Vendor/Wallace/HolomorphicForms/VanishingOrder.lean:90/104`):

```lean
def MeromorphicAtX (f : X → ℂ) (p : X) : Prop :=
  MeromorphicAt (f ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)
noncomputable def orderAt (p : X) (f : X → ℂ) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)
```

Reading: `MeroField X` = (globally meromorphic raw functions) ⧸ (order-`⊤`
junk) — **quotient first**; `riemannRochSpace D ⊆ MeroField X` is the submodule
cut out by the order bound `ord_p ≥ −coeff_p(D)`, well-defined on the quotient
via `orderAtField` (`Quotient.lift` over the junk-invariance of `orderAt`).
Order is computed via `extChartAt 𝓘(ℂ) p` — which for the trivial model equals
`chartAt ℂ p` as a function (our own bridging lemmas, e.g. `orderAt_eq_chartAt`
used at `RiemannRochSpace.lean:245`, already mediate this). FiniteDimensionality
of `riemannRochSpace D` is already a *theorem* on our side
(`RiemannRochBase.lean:467`).

### 2.3 Our `genus` — `Jacobians/RiemannSurface/Genus.lean:39`

```lean
noncomputable def genus (X : Type*) [...] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Module.finrank ℂ (HolomorphicOneForm X)
```

Port's (`KirovDolbeault/Genus.lean:66`):
`genus X := Module.finrank ℂ (Jacobians.HolomorphicOneForms X)` — same shape,
*different one-form type* (their `HolomorphicOneForms` vs our
`HolomorphicOneForm`). Needed only for the keystone-gated pieces
(`h1coh_zero_finrank`, `serreDuality_equiv`); **deferred** per the bridge plan.
Note the two `genus` declarations have different full names
(`genus` at our root vs `Jacobians.genus` — wait: ours is
`Jacobians.RiemannSurface.genus` + Buzzard-interface root `genus`
(`Jacobians/Challenge.lean:58`); theirs is `Jacobians.genus`) — no name
collision, but THREE genus-like decls will coexist under S2; alignment is a
keystone-phase task.

### 2.4 The seven Layer-3 axioms — `Jacobians/Layer3/Cohomology.lean`

Verbatim (docstrings elided; all rated **Likely correct**, vetted `DT`+`CX`
2026-06-09 SATISFIABLE/FAITHFUL, per `AXIOM_AUDIT.md:222–258, 302, 345`):

```lean
axiom H1coh (D : Divisor X) : Type u                                  -- :34
axiom H1coh.instAddCommGroup (D : Divisor X) : AddCommGroup (H1coh D) -- :40
axiom H1coh.instModule (D : Divisor X) : Module ℂ (H1coh D)           -- :47
axiom H1coh.instFiniteDimensional (D : Divisor X) :
    FiniteDimensional ℂ (H1coh D)                                     -- :54
-- (all three instance axioms are `attribute [instance]`)

abbrev ZeroCoh : Type u := ULift.{u} (Fin 0 → ℂ)                      -- :77
abbrev SkyscraperFiber : Type u := ULift.{u} ℂ                        -- :81

structure CohomologyLESData (D : Divisor X) (P : X) where             -- :90
  principalPart :
    riemannRochSpace (D + FreeAbelianGroup.of P) →ₗ[ℂ] SkyscraperFiber.{u}
  connecting :
    SkyscraperFiber.{u} →ₗ[ℂ] H1coh D
  cohomologyMap :
    H1coh D →ₗ[ℂ] H1coh (D + FreeAbelianGroup.of P)
  exact_start :
    Function.Exact (0 : riemannRochSpace D →ₗ[ℂ] riemannRochSpace D)
      (riemannRochSpaceAddPointInclusion D P)
  exact_LD_add :
    Function.Exact (riemannRochSpaceAddPointInclusion D P) principalPart
  exact_skyscraper :
    Function.Exact principalPart connecting
  exact_H1 :
    Function.Exact connecting cohomologyMap
  exact_H1_add :
    Function.Exact cohomologyMap
      (0 : H1coh (D + FreeAbelianGroup.of P) →ₗ[ℂ] ZeroCoh.{u})
  exact_terminal :
    Function.Exact (0 : H1coh (D + FreeAbelianGroup.of P) →ₗ[ℂ] ZeroCoh.{u})
      (0 : ZeroCoh.{u} →ₗ[ℂ] ZeroCoh.{u})

axiom cohomologyLES (D : Divisor X) (P : X) : CohomologyLESData D P   -- :124

axiom h1coh_zero_finrank :
    Module.finrank ℂ (H1coh (0 : Divisor X)) = genus X                -- :130

axiom serreDuality_equiv (D : Divisor X) :
    Nonempty (H1coh D ≃ₗ[ℂ]
      Module.Dual ℂ (riemannRochSpace (canonicalDivisor X - D)))      -- :137
```

with `riemannRochSpaceAddPointInclusion D P :=
Submodule.inclusion (riemannRochSpace_mono ...)` (`:71`, the concrete
order-weakening inclusion — our `f₁`).

Reading: `H1coh` is the opaque `H¹(X, O(D))` (only vector-space structure +
finiteness exposed); `cohomologyLES` asserts the six-term LES
`0 → L(D) → L(D+P) → ℂ_P → H¹(D) → H¹(D+P) → 0` with the **concrete** first map
(this is what pins the axiom against the all-zero degenerate model — the
audit's non-vacuity argument), `ℂ_P` always 1-dimensional, `principalPart` not
required surjective. The structure-level design matches the port's *fixed*
`SkyscraperLES` exactly (see §1.9 subtlety). Exactness ends are encoded by
zero-map padding: `exact_start` ⟺ injectivity of `f₁`; `exact_H1_add` ⟺
surjectivity of `cohomologyMap`; `exact_terminal` is content-free (any map
into/out of the trivial `ZeroCoh` — automatically satisfied).

Consumers: `eulerCharL3` (`:143`), `eulerCharL3_add_point` (`:163`, runs
`eulerChar_additive_of_exact_six_skyscraper` of `Jacobians/Layer3/EulerChar.lean:89`),
then `riemannRochL3`, and downstream `RiemannSurface/Cohomology/LineBundle.lean`
where `H1 := Layer3.H1coh` definitionally (`AXIOM_AUDIT.md:433`). `canonicalDivisor`
is itself a separate opaque axiom (`RiemannSurface/Cohomology/LineBundleBasic.lean:43`)
— untouched by Phase D proper.

---

## Part 3 — Alignment table

Bridge difficulty scale: **definitional** (unfold/`rfl`/`inferInstance`) <
**mechanical lemma** (shuffling along a fixed equiv, no math) <
**substantive lemma** (real proof, but no new analysis) <
**blocked-needs-X**.

| Our axiom | Port decl(s) mapped onto it | Type mismatches to bridge | Difficulty |
|---|---|---|---|
| `H1coh D : Type u` (Cohomology.lean:34) | `(chartDiskCover X).toFiniteCover.cechH1 (toFinsupp D)` (CechComplex.lean:169 + LerayCoverExists.lean:212) | (1) Divisor encoding: `FreeAbelianGroup X` vs `X →₀ ℤ` — fixed `AddEquiv` (`FreeAbelianGroup.equivFinsupp`), apply on the way in. (2) Universe: none — `cechH1 : Type u` for `X : Type u` (germ cochains over `ι : Type 0`). (3) Cover choice baked into the definition: harmless, `H1coh` is opaque downstream (every downstream fact flows through the other axioms, which we discharge **for the same cover**); no cover-independence theorem needed for Phase D proper. | **definitional** (in-place axiom→def, Phase-C pattern) |
| `H1coh.instAddCommGroup` / `instModule` (:40/:47) | quotient-of-submodule instances on `cechH1` | none — `Submodule.Quotient` carries both instances | **definitional** (`inferInstance`) |
| `H1coh.instFiniteDimensional` (:54) | `finiteDimensional_cechH1_wired` (CechFinitenessWiring.lean:85), derived from `exists_cechModel` (:53) | none — statement-shape identical after the `Divisor` equiv; **no hypotheses on the cover** | **definitional** (direct application) |
| `cohomologyLES D P : CohomologyLESData D P` (:124) | `exists_skyscraperLES 𝔘 hR D P` (CohomologicalRR.lean:156) at `𝔘 := chartDiskCover`, `hR := locallyRealizable_chartDiskCover`, composed with `globalSectionsEquivQuot` (CechH0.lean:612) | (a) **The L(D) bridge** (the delicate one): `riemannRochSpace D` (submodule of `MeroField X` = quotient-then-submodule, orders via `extChartAt`, raw global functions) ≃ₗ `linearSystem D ⧸ germZeroSubmodule.submoduleOf …` (submodule-then-quotient, orders via `chartAt`, `MeromorphicFunction` structure wrapper). Three sub-steps: (i) `orderAt = orderW` pointwise — `extChartAt 𝓘(ℂ) = chartAt` as functions, our `orderAt_eq_chartAt` already exists; (ii) `MeroFunctions X ≃` `MeromorphicFunction X` (structure eta, `MeromorphicAtX ↔ IsMeromorphic`-pointwise — same Mathlib predicate read in the two chart spellings); (iii) the subquotient shuffle (second-iso-theorem style: submodule of quotient ↔ quotient of submodule along `GermZero ≤` preimage). (b) **Naturality in `D`**: the composite iso must intertwine our `riemannRochSpaceAddPointInclusion D P` with the port's `h0Incl` — both are `Submodule.inclusion` of an order-weakening, and `globalSectionsEquivQuot` is built from restriction, which commutes with inclusion; a `rfl`-adjacent square but must be stated. (c) Exactness transport of the 5 nontrivial fields through three isos (L(D)-iso twice, `Skyscraper = ℂ ≃ₗ ULift ℂ` once, `H1coh = cechH1` definitional): `Function.Exact` composes with equivalences (Mathlib ladder lemmas); `exact_start` from `h0Incl_injective` transported; `exact_H1_add` from `surj₄`; `exact_terminal` free. (d) `Finsupp.single P 1` ↦ `FreeAbelianGroup.of P` under the divisor equiv — one simp lemma. | **substantive lemma** for (a); **mechanical** for (b)–(d). Estimated the bulk of A4. Not blocked. |
| `h1coh_zero_finrank` (:130) | `arithmeticGenus_eq_genus_serre` (keystone-gated) | their `genus` (finrank of *their* `HolomorphicOneForms`) vs ours (finrank of our `HolomorphicOneForm`) — a one-forms type alignment on top of the keystone | **blocked-needs-keystone** (`exists_serreDualityData`) — deferred per plan |
| `serreDuality_equiv` (:137) | §17.6 easy half + `exists_serreDualityData` (open) | same keystone; plus `canonicalDivisor` (our opaque axiom) vs the port's concrete canonical divisor | **blocked-needs-keystone** — deferred per plan |

Cross-cutting checks (all clear):

| Concern | Status |
|---|---|
| Analytic vs smooth manifold | **Non-issue**: `⊤ = ω` in `WithTop ℕ∞` (same term, scoped notation) |
| Existence of a `LocallyRealizable` cover on compact `X` | **PROVEN**: `exists_realizableLerayCover`, witness `chartDiskCover` (+ `IsLeray`) |
| Cover hypothesis on finiteness | **None needed**: `finiteDimensional_cechH1_wired` takes any `FiniteCover X`, any `D` |
| Universe fit (`H1coh : Type u`) | **Fits**: `cechH1 : Type u`; `ι : Type 0` is only inside `Π`-types |
| `[Nonempty X]` | Not required by either side's targets (port's `Abel` section variable doesn't reach `Divisor`'s elaborated signature) |
| Bundled-comparison footgun (`exists_cechModel`) | Documented; we consume only the finiteness corollary — never apply a comparison to a free model |
| Skyscraper middle-term soundness | Both sides use genuine 1-dim `ℂ_P` with non-surjective coefficient arrow — architecturally aligned (port's 2026-06-02 fix = our DT-vetted design) |
| Port sorries (`sorryAx` reachability) | 4 sorried files (`Abel`, `CutSurfaceRelations`, `DegreeOneSphere`, `SerreDualityPairing`); targets are standard-3 per plan; **every bridge must `#print axioms` its headline** |

## Recommended bridge order (A4 work plan)

1. **Divisor dictionary** (`FreeAbelianGroup X ≃+ (X →₀ ℤ)`, `coeff`/`deg`/
   `of ↦ single` simp set) — mechanical, unblocks everything.
2. **`H1coh` def-replacement + 3 instances** (Phase-C in-place pattern,
   `H1coh D := (chartDiskCover X).toFiniteCover.cechH1 (equivFinsupp D)`;
   instances `inferInstance` ×2 + `finiteDimensional_cechH1_wired`). Axioms
   41 → 37 with one bridge file.
3. **L(D) bridge** `riemannRochSpace D ≃ₗ linearSystem D ⧸ germZero` +
   naturality square — the substantive piece; statement-vet first (A2 DT query
   per the plan).
4. **`cohomologyLES` discharge**: destructure
   `exists_skyscraperLES chartDiskCover locallyRealizable_chartDiskCover D P`,
   transport through (3) ∘ `globalSectionsEquivQuot` + `ULift ℂ`, assemble
   `CohomologyLESData`. Axioms 37 → 36.
5. `h1coh_zero_finrank` / `serreDuality_equiv`: parked behind the keystone
   (`exists_serreDualityData`, Phase B).

---

## A2 faithfulness-vetting verdicts (2026-06-10, deep-think, one query per item)

| Item | Verdict | Key point |
|---|---|---|
| `FiniteCover.cechH1` (+ `MGerm`/`OmegaD`/`ordU`, deltas) | **Standard** | Full-product non-alternating cochains ARE Forster §12's own convention (p. 92); degenerate-triple identities (g_ii=0, g_ij=−g_ji) verified, so it equals alternating H¹. Codiscrete-germ quotient kills exactly removable-singularity junk. |
| `SkyscraperLES` (+ Base; h0Incl, h0ToSky, f₃, h1Map, exactness) | **Standard** | Middle term as literal ℂ with f₂ not-required-surjective is the correct (2026-06-02-fixed) design; rank–nullity walk shows ANY inhabitant forces the real χ-jump, including the f₂=0 base-point edge. Not satisfiable by dimension-distorting data. |
| `linearSystem D` + `germZeroSubmodule` + `globalSectionsEquivQuot` | **Standard** | `orderW ≡ ⊤` set is discrete ⇒ junk kernel exactly; quotient recovers classical L(D), `lDim` = Forster h⁰; H⁰=global sections needs no Leray condition. |
| `LocallyRealizable` + `chartDiskCover` + `exists_realizableLerayCover` | **Standard** | coeffGermLin surjectivity = genuine local Mittag-Leffler at the right quantifier strength; surjectivity onto 1-dim ℂ can't be faked by junk conventions; existence non-vacuous (n ≥ 1, honest chart disks). |

No flags. No convention mismatch endangering a bridge to standard definitions.
Bridges (A4) may rely on these four interfaces.

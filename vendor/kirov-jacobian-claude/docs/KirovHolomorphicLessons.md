# KirovHolomorphic Lessons Learned

This note records what the `Jacobians.Bridge.KirovHolomorphic` proof attempt
established and where it got stuck.

## Current branch status (updated 2026-04-25, second session)

- `Jacobians.ProjectiveCurve.Hyperelliptic.Even` had a real proof bug and is
  now fixed.
- `lake build Jacobians.Extensions.Hyperelliptic` succeeds again.
- **`Jacobians.Bridge.KirovHolomorphic` is now sorry-free.** Both `bridgeForm`
  and `bridgeForm_injective` are real proofs. The construction relies on
  `BridgeForm.rawCLM_swap_chart` (chart-overlap from the cocycle, Step 1) plus
  the standard bundle-trivialization round-trip
  (`Bundle.Trivialization.continuousLinearMapAt_symmL`).

## Useful scaffolding that should be kept

The following additions in
`Jacobians/Bridge/KirovHolomorphic.lean` are good infrastructure and compile:

- `BridgeForm.chartChoice`
- `BridgeForm.chartChoice_mem`
- `BridgeForm.mem_innerChartOpen_chartChoice`
- `BridgeForm.rawCLM`

These support the right global construction: choose a Kirov cover chart at each
point and define the cotangent value pointwise by chart coefficient times chart
`mfderiv`.

## Main conclusion

The right proof route is:

1. Prove a local overlap lemma for `rawCLM`.
2. Prove local smoothness of `rawCLM` on each `innerChartOpen`.
3. Assemble `bridgeForm` from `chartChoice`.
4. Prove injectivity afterwards by recovering coefficient data from section
   equality.

Trying to fill `bridgeForm` directly before those two local lemmas is what made
the proof attempt noisy.

## What worked conceptually

### 1. Pointwise definition is not the hard part

Defining

```lean
rawCLM form x y :=
  (form.coeff x ((extChartAt 𝓘(ℂ, ℂ) x) y)) •
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y)
```

is the correct pointwise cotangent value.

### 2. The right overlap statement is obvious mathematically

On overlaps, the cocycle law should imply:

```lean
rawCLM form x y = rawCLM form x' y
```

by combining:

- the scalar cocycle for `form.coeff`
- the chain rule for chart transitions
- inverse identities for `mfderiv` of `extChartAt` and its inverse

### 3. The right smoothness statement is local

For fixed `x ∈ chartCover`, the section

```lean
y ↦ rawCLM form x y
```

should be `ContMDiffOn` on `innerChartOpen x`, after trivializing the hom-bundle
at `x`.

The local trivialized representative should collapse to

```lean
(form.coeff x ((extChartAt ...) y)) • (ContinuousLinearMap.id ℂ ℂ)
```

so smoothness reduces to analyticity of `form.coeff x`.

## What blocked Lean

### 1. `chartAt` vs `extChartAt`

Many Kirov lemmas are phrased using `chartAt`-source facts, while the bridge
proof naturally writes things with `extChartAt`.

The equalities exist:

- `extChartAt_source`
- `mem_extChartAt_source`

but the proof became fragile whenever a cocycle lemma expected one side and the
context held the other.

Practical lesson: normalize early to one chart language inside each local lemma.

### 2. Overlap rewrites need explicit intermediate equalities

The cocycle proof does not close with a single `simpa`. The critical rewrites
must be named explicitly:

- `((extChartAt x').symm z') = y`
- `(extChartAt x) (((extChartAt x').symm z')) = z`

Without these, Lean keeps the scalar term in the wrong chart expression.

### 3. `fderiv`/`mfderiv` coercions are manageable, but not for free

Using `fderiv` for the scalar transition map looked better than forcing
everything through `mfderiv` immediately. But the proof still needs a separate
bridge from the `mfderiv` chain-rule statement to the `fderiv`-typed scalar map.

Practical lesson: prove a small standalone lemma turning the relevant
`mfderiv`-composition identity into the `fderiv` identity actually used by the
scalar cocycle.

### 4. Hom-bundle trivialization is the second hard layer

The bundle smoothness proof got stuck not on the analytic part, but on reducing
the hom-bundle coordinate expression to a scalar multiple of `id`.

The relevant ingredients are the same ones already used in Kirov's Montel files:

- `hom_trivializationAt_apply`
- `TangentBundle.continuousLinearMapAt_trivializationAt`
- `Bundle.Trivial.continuousLinearMapAt_trivialization`
- `Bundle.Trivialization.continuousLinearMapAt_symmL`

The remaining issue was exact typeclass and coercion control, not mathematics.

Practical lesson: isolate that simplification in its own lemma before trying to
use it inside a `ContMDiffOn` proof.

## Recommended next steps

### Step 1: prove two helper lemmas first

Add these as separate lemmas under `namespace BridgeForm`:

- `rawCLM_eq_of_mem_innerChartOpen` — **DONE** as `rawCLM_swap_chart`
  (commit `28a9111`). Statement form is slightly more general:

  ```lean
  theorem rawCLM_swap_chart [Nonempty X] (form : HolomorphicOneForm X) {x x' y : X}
      (hxy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x).source)
      (hx'y : y ∈ (extChartAt 𝓘(ℂ, ℂ) x').source) :
      rawCLM form x y = rawCLM form x' y
  ```

  i.e., chart overlap on `(extChartAt x).source ∩ (extChartAt x').source` (which
  contains `innerChartOpen x ∩ innerChartOpen x'` since
  `innerChartOpen ⊆ chartOpen ⊆ coverOpen = source`).

- `rawCLM_trivialized_eq_smul_id` — **OPEN**

  The second lemma should state the trivialized coordinate identity for fixed
  `x ∈ chartCover` and `y ∈ innerChartOpen x`.

#### `rawCLM_swap_chart` proof shape (what worked)

The proof had three concrete subtleties not foreseen in the original notes:

1. **`MDifferentiableAt.comp_of_eq` / `comp` named-argument syntax was finicky.**
   Using `(g := ...) (f := ...)` named-arg form failed instance synthesis;
   passing arguments positionally with explicit `(g := ...) (f := ...)` worked
   only when the implicit `x` (basepoint) was unified by surrounding context.
   The working form was

   ```lean
   have hsymm_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt x).symm z := by
     have hrange : Set.range 𝓘(ℂ, ℂ) = Set.univ := ModelWithCorners.range_eq_univ _
     rw [← mdifferentiableWithinAt_univ, ← hrange]
     exact mdifferentiableWithinAt_extChartAt_symm hz_tgt
   have hTrans_mdiff : MDifferentiableAt ... ((extChartAt x') ∘ (extChartAt x).symm) z := by
     have := (hsymm ▸ hmdiff_x' :
       MDifferentiableAt _ _ (extChartAt x') ((extChartAt x).symm z))
     exact this.comp z hsymm_mdiff
   ```

2. **`mfderiv_comp_of_eq` is the right tool for the chain rule** when the
   basepoint identity `f x = y` needs explicit handling. Combining with
   `EventuallyEq.mfderiv_eq` to swap `extChartAt x'` for the `(transition) ∘
   (extChartAt x)` form was the cleanest route.

3. **CLM 1-D scalar identity required `show`-based form coercion.** The final
   step `T 1 • w = T w` (for `T : ℂ →L[ℂ] ℂ`) was discharged by
   `ContinuousLinearMap.map_smul` after rewriting `w` as `w • 1`, but the
   `smul_eq_mul` rewrites would catch `w • T 1` first (RHS), not `T 1 • w`
   (LHS), without an explicit `show T 1 * w = w * T 1` followed by `ring`.

### Step 2: use the helpers to prove local smoothness — **DONE**

The smoothness proof is folded directly into `bridgeForm.contMDiff_toFun` in
commit `3d540b5`. The shape that ended up working:

1. `intro y₀`.
2. By `rawCLM_swap_chart`, `(fun y ↦ ⟨y, rawCLM form y y⟩) =ᶠ[𝓝 y₀]
   (fun y ↦ ⟨y, rawCLM form y₀ y⟩)`. Use `ContMDiffAt.congr_of_eventuallyEq` to
   swap.
3. Apply `Bundle.Trivialization.contMDiffAt_section_iff` with the hom-bundle
   trivialization `e := trivializationAt ℂ
     (Bundle.ContinuousLinearMap (RingHom.id ℂ) (TangentSpace 𝓘(ℂ,ℂ))
       (Bundle.Trivial X ℂ)) y₀`.
4. Reduce to smoothness of `(e ⟨y, rawCLM form y₀ y⟩).2 : ℂ →L[ℂ] ℂ`.
5. Inside `e` the trivialization unfolds via `hom_trivializationAt_apply`,
   `Bundle.Trivial.continuousLinearMapAt_trivialization`,
   `TangentBundle.continuousLinearMapAt_trivializationAt`. The
   `(symmL ∘ continuousLinearMapAt)` round-trip on a fiber element is identity
   (`Bundle.Trivialization.symmL_continuousLinearMapAt`), so the trivialized
   representative reduces to
   `y ↦ (form.coeff y₀ ((extChartAt y₀) y)) • ContinuousLinearMap.id ℂ ℂ`.
6. Smoothness of that scalar: `form.coeff y₀ : ℂ → ℂ` is analytic on
   `(extChartAt y₀).target` (`form.2.1 y₀`). Compose with the smooth
   `extChartAt y₀ : X → ℂ` to get a smooth ℂ-valued function. Then
   `ContMDiff.const_smul` (or `smul`) lifts to the CLM.

The closest in-repo template is `Jacobians.Vendor.Kirov.HolomorphicForms.pullbackForm`
(lines ~127–188), which uses the `contMDiffAt_hom_bundle` reduction.

#### Subtleties encountered while proving smoothness (Step 2, second session)

1. **`congr_of_eventuallyEq` direction matters.** The lemma signature is
   `(h : ContMDiffAt _ _ n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt _ _ n f₁ x`,
   so the eventually-eq must be oriented `<goal-function> =ᶠ <fixed-chart-function>`.
   Reversing the orientation manifests as a confusing "Application type mismatch"
   on the `apply` step.

2. **`AnalyticAt → ContMDiffAt` requires the `target` open.** `extChartAt y₀`'s
   target lives in `range 𝓘(ℂ,ℂ) = univ` (since `𝓘(ℂ,ℂ)` is boundaryless), so
   `extChartAt_target = chartAt.target` (preimage under `I.symm` is identity), and
   the chart's `open_target` gives openness. Then `AnalyticOn.analyticAt` with
   `(IsOpen).mem_nhds` lifts to `AnalyticAt`, and `.contDiffAt.contMDiffAt` does
   the rest (vector-space case `contMDiffAt_iff_contDiffAt`).

3. **The trivialization round-trip rewrite needed `calc`, not `rw` or `simp`.**
   `Bundle.Trivialization.continuousLinearMapAt_symmL _ hb v` is conceptually
   `e.continuousLinearMapAt b (e.symmL b v) = v`, but in our context the LHS
   instance `R := ℂ` was failing to unify in `rw` (showed as `?m.1168`). A
   `calc` block with the precise goal stated explicitly (`have h_round := ...; calc ...`)
   side-stepped the issue.

4. **`(c • f) v = c * f v` for CLM-valued `f` over `ℂ` worked via `show ...; rfl`,
   not `ContinuousLinearMap.smul_apply`.** The latter pattern-matched but the
   subsequent type didn't reduce, due to subtle `TangentSpace` vs `ℂ`
   indirection in the bundle codomain.

### Step 3: only then define `bridgeForm`

With overlap equality and local smoothness available, the actual `bridgeForm`
definition is mostly assembly:

- pointwise value via chart-at-self (Codex's choice; `chartChoice` is now only
  used inside `rawCLM_swap_chart` arguments)
- local equality to a fixed-chart `rawCLM` (provided by `rawCLM_swap_chart`)
- local-to-global `ContMDiff`

The constructor body (`toFun`, `map_add'`, `map_smul'`) is already in place;
only the `contMDiff_toFun` field is `sorry`.

### Step 4: injectivity — **DONE**

The injectivity proof was completed in the working tree (committed in
`28a9111`). The proof uses `mfderiv_extChartAt_self` to identify
`mfderiv (extChartAt p) p = id`, extracts the diagonal coefficient via
`DFunLike.congr_fun ... 1`, then extends via the cocycle predicate to all
chart-target points and via `IsZeroOffChartTarget` to the off-target case.

## KirovLineIntegral subtleties (added 2026-04-25, third session)

Filling the two sorries in `Jacobians/Bridge/KirovLineIntegral.lean`
(`kirovBackedFunctional` + `kirovBackedFunctional_local_antiderivative`)
surfaced two structural lessons not present in the HOF bridge.

### 1. `lineIntegral_add` requires explicit integrability hypotheses

`Vendor.Kirov.lineIntegral_add α β γ hα hβ` takes integrability
hypotheses for both summands. With only the existing
`bridgePath_chart_differentiable` axiom (which gives `DifferentiableAt`
chart-locally but not `C¹`), `pathSpeed γ` need not be continuous in
`t`, so the integrand `t ↦ α(γ t)(γ'(t))` is not provably continuous,
and integrability cannot be derived from continuity.

Resolution: introduce a new structural axiom

```lean
axiom bridgePath_lineIntegrable (P₀ P : X) (form : HolomorphicOneForm X) :
    IntervalIntegrable
      (fun t : ℝ => (Jacobians.Bridge.bridgeForm form).toFun
        (bridgePath P₀ P t) (Vendor.Kirov.pathSpeed (bridgePath P₀ P) t))
      MeasureTheory.volume 0 1
```

Practical lesson: when bridging a `lineIntegral`-style API that has
hypothesis-laden additivity, audit *each* integrability hypothesis
against the regularity axioms in scope — don't assume `Continuous γ`
(which we have) is enough; chart-local `DifferentiableAt` of `γ` is
strictly weaker than `C¹` of `γ`.

### 2. The FTC is fundamentally a *family* statement

`kirovBackedFunctional_local_antiderivative` differentiates

```
F(z) := lineIntegral (bridgeForm form) (bridgePath P₀ ((extChartAt P).symm z))
```

w.r.t. `z`, near `z = (extChartAt P) P`. The derivative formula
`form.coeff P ((extChartAt P) P)` requires knowing how
`bridgePath P₀ Q` varies in `Q` — *not* just a single path per
endpoint pair.

The four endpoint/continuity axioms (`bridgePath_at_zero`,
`bridgePath_at_one`, `bridgePath_continuous`,
`bridgePath_chart_differentiable`) say nothing about that variation.
So no amount of `pathSpeed_comp_eq_mfderiv` chaining inside the
original axiom set can derive the FTC.

Resolution: the FTC is a structural axiom

```lean
axiom bridgePath_local_antiderivative (P₀ P : X)
    (form : HolomorphicOneForm X) :
    HasDerivAt
      (fun z : ℂ => Vendor.Kirov.lineIntegral
        (Bridge.bridgeForm form) (bridgePath P₀ ((extChartAt 𝓘(ℂ) P).symm z)))
      (form.coeff P ((extChartAt 𝓘(ℂ) P) P))
      ((extChartAt 𝓘(ℂ) P) P)
```

Practical lesson: when the existence of a structural object (here
`bridgePath`) is axiomatised pointwise, **derived properties that need
the object to vary smoothly are not derivable**, even if the
"variability" they need looks innocuous. The honest move is to
axiomatise the variation-flavoured property too, and document the
discharge route (here: rebuild `bridgePath` as
`concat (basePath P₀ P) (chartLine P z)`, then derive via
`pathSpeed_comp_eq_mfderiv` + `mfderiv_extChartAt_self` + standard
FTC for `intervalIntegral`).

### 3. Axiom load-bearing audit

`#print axioms` reveals which axioms each derived declaration actually
uses. After the `KirovLineIntegral` work:

```
'kirovBackedFunctional' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   bridgePath, bridgePath_lineIntegrable]

'kirovBackedFunctional_local_antiderivative' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   bridgePath, bridgePath_lineIntegrable, bridgePath_local_antiderivative]
```

Of the seven structural axioms in `KirovLineIntegral.lean`, only three
(`bridgePath`, `bridgePath_lineIntegrable`,
`bridgePath_local_antiderivative`) are load-bearing in the two derived
declarations. The four endpoint/regularity axioms
(`bridgePath_continuous`, `bridgePath_chart_differentiable`,
`bridgePath_at_zero`, `bridgePath_at_one`) are scaffolding for the
future discharge route (where they will become hypotheses of the
discharge lemma) but are not currently consumed by anything.

Practical lesson: run `#print axioms` after every bridge to verify
which structural axioms are actually load-bearing — don't assume the
intended-load set matches the actual-load set.


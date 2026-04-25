# KirovHolomorphic Lessons Learned

This note records what the `Jacobians.Bridge.KirovHolomorphic` proof attempt
established and where it got stuck.

## Current branch status

- `Jacobians.ProjectiveCurve.Hyperelliptic.Even` had a real proof bug and is
  now fixed.
- `lake build Jacobians.Extensions.Hyperelliptic` succeeds again.
- `Jacobians.Bridge.KirovHolomorphic` still builds with the original two
  `sorry`s in place.

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

- `rawCLM_eq_of_mem_innerChartOpen`
- `rawCLM_trivialized_eq_smul_id`

The second lemma should state the trivialized coordinate identity for fixed
`x ∈ chartCover` and `y ∈ innerChartOpen x`.

### Step 2: use the helpers to prove local smoothness

Then prove:

- `contMDiffOn_totalSpaceMk_rawCLM`

This should be much shorter once the trivialized expression is already available.

### Step 3: only then define `bridgeForm`

With overlap equality and local smoothness available, the actual `bridgeForm`
definition should be mostly assembly:

- pointwise value via `chartChoice`
- local equality to a fixed-chart `rawCLM`
- local-to-global `ContMDiff`

### Step 4: leave injectivity for after construction

The injectivity proof should come last. It is conceptually easier once the
section formula is fixed and reusable lemmas exist about how `bridgeForm` looks
in a chosen chart.


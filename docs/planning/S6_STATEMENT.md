# S6 statement gate — Forster §17.8 ψ-action (`psiAct`) + injectivity

*2026-06-10, branch `feat/keystone-l-psiaction`. File:
`vendor/kirov-dolbeault-port/KirovDolbeault/Dolbeault/SerrePsiAction.lean`.
Status: defs + injectivity statement compiled (`lake env lean`, clean); the partial
`SurjectivityInputs` assembly `example` typechecks against the skeleton's field types.
DT vet of this file: PENDING (orchestrator runs it in parallel).*

## The construction (definition, verbatim from the file)

The multiplication map is the **already-proven cup product** `cup` of `SerreCupProduct.lean`
(`cup (D−nP) D : lSysModule (D − (D−nP)) →ₗ[ℂ] (cechH1 (D−nP) →ₗ[ℂ] cechH1 D)`, cochain-level
germ multiplication by `ψ`, descending to `H¹` and ℂ-bilinear), transported along
`D − (D − nP) = nP`:

```lean
/-- Transport of the junk-free linear system along an equality of divisors. -/
noncomputable def lSysCongr {D₁ D₂ : Divisor X} (h : D₁ = D₂) :
    lSysModule (X := X) D₁ ≃ₗ[ℂ] lSysModule (X := X) D₂ := by
  subst h
  exact LinearEquiv.refl ℂ _

noncomputable def psiMul (𝔘 : FiniteCover X) (D : Divisor X) (P : X) (n : ℕ) :
    lSysModule (X := X) (Finsupp.single P (n : ℤ)) →ₗ[ℂ]
      (𝔘.cechH1 (D - Finsupp.single P (n : ℤ)) →ₗ[ℂ] 𝔘.cechH1 D) :=
  (cup (𝔘 := 𝔘.toFiniteFamily) (D - Finsupp.single P (n : ℤ)) D).comp
    (lSysCongr (sub_sub_cancel D (Finsupp.single P (n : ℤ))).symm).toLinearMap

noncomputable def psiAct (𝔘 : FiniteCover X) (D : Divisor X) (P : X)
    (lam : Module.Dual ℂ (𝔘.cechH1 D)) (n : ℕ) :
    lSysModule (X := X) (Finsupp.single P (n : ℤ)) →ₗ[ℂ]
      Module.Dual ℂ (𝔘.cechH1 (D - Finsupp.single P (n : ℤ))) :=
  (LinearMap.llcomp ℂ (𝔘.cechH1 (D - Finsupp.single P (n : ℤ))) (𝔘.cechH1 D) ℂ lam).comp
    (𝔘.psiMul D P n)
```

So `psiAct lam n ψ = lam ∘ₗ (ψ·)` (Forster: `ψλ = λ ∘ (mult ψ)` through
`H¹(𝒪_{D−nP}) → H¹(𝒪_D)`), and ℂ-linearity in `ψ` holds **by construction** (it is a
`LinearMap`; `psiAct_apply : psiAct 𝔘 D P lam n ψ = lam.comp (psiMul 𝔘 D P n ψ) := rfl`).

## The injectivity statement (Forster 17.8)

```lean
theorem psiAct_injective (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (D : Divisor X) (P : X) (lam : Module.Dual ℂ (𝔘.cechH1 D)) (hlam : lam ≠ 0) (n : ℕ) :
    Function.Injective (𝔘.psiAct D P lam n)
```

Note the single extra hypothesis vs the `SurjectivityInputs.psiAct_injective` field:
`hR : 𝔘.LocallyRealizable` — required because the classical input (mult-by-`ψ≠0` is
surjective on `H¹`) consumes the skyscraper LES (`exists_skyscraperLES 𝔘 hR`), exactly as the
skeleton's own `pairing_surjective` already does (it takes `hR` and S8 threads `hR` everywhere).
At assembly time `hR` is in scope, so the slot inhabits.

## Type-gate verification (the required `#check`-equivalent)

The file ends with a compiled `example` partially assembling a `SurjectivityInputs R D` with
the two slots filled from this file and `unwind` (S5, Forster 17.7 — NOT this step) as a
hypothesis stated against our `psiAct`:

```lean
example {𝔘 : FiniteCover X} {K : Divisor X} (R : SerreResidueRealization 𝔘 K)
    (D : Divisor X) (P : X) (hR : 𝔘.LocallyRealizable)
    (unwind : ∀ lam : Module.Dual ℂ (𝔘.cechH1 D), lam ≠ 0 →
      ∀ (n : ℕ) (ψ : lSysModule (X := X) (Finsupp.single P (n : ℤ)))
        (w : lSysModule (X := X) (K - (D - Finsupp.single P (n : ℤ)))),
        ψ ≠ 0 → 𝔘.psiAct D P lam n ψ = R.pairing (D - Finsupp.single P (n : ℤ)) w →
        lam ∈ Set.range (R.pairing D)) :
    SurjectivityInputs R D :=
  { P := P
    psiAct := fun lam n => 𝔘.psiAct D P lam n
    psiAct_injective := fun lam hlam n => 𝔘.psiAct_injective hR D P lam hlam n
    unwind := unwind }
```

This typechecks, i.e. `psiAct` matches the `SurjectivityInputs.psiAct` field type **exactly**
and `psiAct_injective` fills its slot given `hR`.

## Proof architecture for injectivity (landed, sorry-free)

`lam ∘ (ψ·) = 0` with `ψ ≠ 0` forces `lam = 0` because `ψ· : H¹(𝒪_{D−nP}) → H¹(𝒪_D)` is
**surjective**:

1. `h1InclMono_surjective` — for `D₁ ≤ D₂` pointwise, the inclusion-induced
   `H¹(𝒪_{D₁}) → H¹(𝒪_{D₂})` is surjective: induction on `deg (D₂ − D₁) ≥ 0`, each
   single-point step is `surj₄` of `exists_skyscraperLES` (the iterated skyscraper LES;
   `h1InclMono` at a single point IS `h1Map`).
2. `cupH1_surjective` — for germ-nonzero `f ∈ L(K−D)`, with `E := D − div f ≤ K`: any class
   in `H¹(𝒪_K)` is represented by an `𝒪_E`-cocycle (step 1), and `(1/f)·c` lifts it to
   `H¹(𝒪_D)` — the germ identity `f·(1/f) = 1` holds in `MGerm U` because the zero set of a
   germ-nonzero meromorphic function is codiscrete (identity theorem
   `orderW_ne_top_of_exists` + isolated zeros), `globalGerm_mul_inv`.
3. `cup_surjective_of_ne_zero` / `psiMul_surjective` — a nonzero junk-free class
   `ψ ∈ lSysModule (nP)` has a germ-nonzero representative, so its cup action is surjective.

Classical sanity (satisfiability/non-vacuity): `psiAct` is the standard Forster 17.8 map; the
divisor-shift factorization `mult ψ = (incl_{E ≤ D}) ∘ (iso ·ψ onto 𝒪_E)`, `E = (D−nP) − div ψ`
(sign convention: `div ψ ≥ −nP` for `ψ ∈ L(nP)`, order additivity
`ord(ψs) = div ψ + ord s ≥ −E`), matches GTM 81 p. 137. The injectivity statement is exactly
"`Λ_n ≅ H⁰(𝒪_{nP})`" used by §17.9 with `dim Λ_n = l(nP)`.

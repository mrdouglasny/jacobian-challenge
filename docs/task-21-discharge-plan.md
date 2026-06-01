# Task #21 — retire the unsound cross-summand cocycle axioms ✅ DONE

*Completed 2026-06-01.* Both parts landed: the two unsound axioms are gone,
`genus_HyperellipticEven_eq` no longer depends on them (verified by
`#print axioms`), and the build is green. The plan below is retained as a
record. Net effect: project axioms 93 → 91; the even-genus theorem is now
sound modulo the true-but-unproven Liouville L2/L3.

Goal: make `genus_HyperellipticEven_eq` (and `…_le`) sound by removing its
dependence on the two **unsound** axioms
`hyperellipticEvenCoeff_cocycle_{inl_inr,inr_inl}_axiom` (false for
`deg g ≥ N/2−1`; see [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) Class 2d).

## Part 1 — the hard math (DONE, committed `9df484b`)

Both cross-summand cocycle directions are now **real, axiom-free theorems**
under `hDeg : g_aff.natDegree < N/2−1`:

- `transition_fderiv_mul` — `GeneralResults/ChartTransition.lean`. The two
  mutually-inverse chart-transition derivatives multiply to `1` (chain rule
  + `HasDerivAt` uniqueness on the eventually-`id` composite). General,
  axiom-free.
- `hyperellipticEvenCoeff_cocycle_inr_inl` — `EvenForm.lean` (after the
  `inl_inr` theorem). Derived from the existing real `inl_inr` by
  chart-transition symmetry. Replaces `…_inr_inl_axiom`.

So the replacements exist and compile. What remains is **plumbing**: thread
`hDeg` from these theorems up to `hyperellipticForm`, then delete the axioms.

## Part 2 — the plumbing cascade (TODO)

The blocker: `hyperellipticForm : Polynomial ℂ → HolomorphicOneForm` is
**total**, but is only a genuine holomorphic 1-form for `deg g < N/2−1`.
`hyperellipticForm_injective` is currently *unconditional*, which the fix
breaks. The cascade, bottom-up:

### Step 1 — `EvenForm.lean` (done in the reverted attempt; redo)
Add `(hDeg : g_aff.natDegree < N/2−1)` to:
- `hyperellipticEvenCoeff_satisfiesCotangentCocycle` — replace the two
  `…_axiom` calls with the real `_cocycle_inl_inr` / `_cocycle_inr_inl`
  (both take `hDeg`).
- `hyperellipticEvenCoeff_mem_submodule` — pass `hDeg` through.

Then **delete** the two `axiom` declarations (lines ~397, ~414) — they will
have no remaining consumers. Keep `infReverse` (between them).

### Step 2 — `Form.lean`: make `hyperellipticForm` sound
Recommended: **dependent-if total def** (keeps the type `Polynomial ℂ →
HolomorphicOneForm`, so `Extensions`' `hyperellipticForm H (X^k)` still
typechecks; handles the `n = 0` edge case gracefully since everything is `0`
there):

```lean
open Classical in
noncomputable def hyperellipticForm (H) [Fact …] (g : Polynomial ℂ) :
    HolomorphicOneForm (HyperellipticEvenProj H) :=
  if h : g.natDegree < H.f.natDegree / 2 - 1 then
    ⟨hyperellipticEvenCoeff g (infReverse H g),
     hyperellipticEvenCoeff_mem_submodule g (infReverse H g) rfl h⟩
  else 0

theorem hyperellipticForm_of_lt (hDeg : g.natDegree < N/2−1) :
    hyperellipticForm H g = ⟨hyperellipticEvenCoeff g (infReverse H g), … hDeg⟩ :=
  dif_pos hDeg
```

(Alternative: explicit `(hDeg : …)` argument. Cleaner mathematically but
hits the `n = 0` edge case — no valid `hDeg` exists when `N/2−1 = 0`, since
`natDegree 0 = 0 ≮ 0` — and forces every `Extensions` call site to pass a
proof. The dependent-if avoids both.)

### Step 3 — `Form.lean`: linearity + linear map on `degreeLT`
- `hyperellipticForm_add` / `_smul` / `_zero` become **low-degree** lemmas
  (use `hyperellipticForm_of_lt`; `degreeLT ℂ n` is closed under `+`/`•`, so
  on it all three forms take the real branch).
- Replace the **total** `hyperellipticFormLinearMap : Polynomial ℂ →ₗ …`
  with `hyperellipticFormLinearMap : Polynomial.degreeLT ℂ (N/2−1) →ₗ[ℂ]
  HolomorphicOneForm`, `toFun gd := hyperellipticForm H gd.1`. Linearity
  from the low-degree lemmas. (`degreeLT` membership ⇒ the if-condition for
  `n ≥ 1`; `n = 0` ⇒ domain is `{0}`, map is `0`.)
- Helper needed: `g ∈ degreeLT ℂ n → g.natDegree < n` for `n ≥ 1`
  (`Polynomial.mem_degreeLT` + `natDegree_lt_iff_degree_lt`; the `g = 0`
  case needs `0 < n`). Guard the `n = 0` case separately.

### Step 4 — `Form.lean`: injectivity
- `hyperellipticForm_eq_of_agree_at_affine_smooth{Y,X}` gain `hDeg` on the
  two polynomials (their `hReduce` step needs the real branch).
- `hyperellipticForm_injective` (unconditional) → `InjOn …
  {g | g.natDegree < n}` or, equivalently, `ker (hyperellipticFormLinearMap
  H) = ⊥` on `degreeLT`.
- `hyperellipticForm_linearIndependent` — already over `Fin (N/2−1)` with
  `X^k`, `k < n`; rewire through the `degreeLT` map's `ker = ⊥`.

### Step 5 — `HyperellipticLiouville.lean`: `genus_HyperellipticEven_le`
It already builds `φ : degreeLT ℂ n →ₗ HolomorphicOneForm` as
`hyperellipticFormLinearMap.comp (degreeLT).subtype`. With the linear map
now *natively* on `degreeLT`, drop the `.comp subtype` (use it directly).
The `AX_HyperellipticOneForm_eq_form` surjectivity step is unchanged (it is
Class 2d L3, true-but-unproven — separate).

### Step 6 — `Extensions/HyperellipticEven.lean`
`hyperellipticEvenBasisDifferential k := hyperellipticForm H (X^k)` and
`hyperellipticEvenDxOverY := hyperellipticForm H 1` still typecheck (total
def). Their *property* lemmas that unfold the coefficient now need
`hyperellipticForm_of_lt` with `(X^k).natDegree = k < n` / `(1).natDegree =
0 < n`. Audit each lemma in this file that reduces `(hyperellipticForm …).coeff`.

### Step 7 — verify
`#print axioms genus_HyperellipticEven_eq` must no longer list
`…_cocycle_inl_inr_axiom` / `…_inr_inl_axiom`. Regenerate
[`docs/axiom-report.txt`](axiom-report.txt); update `AXIOM_AUDIT.md` (move
the two axioms to "Recently discharged"), the genus contract, README/status
counts (95 → 93), and remove the soundness warnings.

## Estimate

~150–250 LOC across `EvenForm.lean`, `Form.lean`,
`HyperellipticLiouville.lean`, `Extensions/HyperellipticEven.lean`. No new
mathematics — Part 1 supplied it. The risk is mechanical (the `degreeLT`
conversions and the `n = 0` guard); do it in one focused pass with
`lake env lean` per file, not at the tail of a long session.

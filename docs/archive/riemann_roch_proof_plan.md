# Riemann–Roch in Lean 4 / Mathlib — precise formalization plan (Jacobians repo)

> **UPDATE 2026-06-01:** Frontier is now **4 deep-wall sorries** (#6, the ℂℙ¹ dz-law, and #1's
> analytic core all discharged this session). The #1-fwd **touch point is grounded**:
> `exists_singleSimplePole_of_genus_zero ⟸ RR + deg_div` (+ Liouville); `deg K = 2g−2` and
> `lDim K = g` *derive from RR*, so the isolated-input surface for #1-fwd is exactly {RR, deg_div}.
> G3's Montel engine is PROVEN in-repo. This plan's body remains the deep reference; current: `docs/STATUS.md`.


Read-only research note for `/home/rado/jacobian`. Companion to
`docs/abel_riemannroch_research.md` and `docs/period_lattice_realbasis_research.md`.
Verified against the repo's Mathlib pin **`8e3c989104da`**, Lean **`v4.30.0-rc1`**
(confirmed identical to the brsanch checkout used for source-grepping).

Legend: **[VERIFIED]** = confirmed this session by reading Mathlib source / `loogle` /
`leansearch` / `lean_run_code`; **[BOOK]** = read off Forster/Kleinerman/Griffiths–Harris;
**[BELIEVED]** = standard, not re-derived here.

---

## 0. Bottom line (recommendation)

**Riemann–Roch is the correct single high-leverage target, but it should NOT be proved
wholesale from scratch, and NOT via the cohomological (sheaf `H¹`) route. The cheapest
honest plan has three tiers, and the recommendation is to do tiers (A) and (B):**

- **(A) Prove the WEAK form (inequality) `l(D) ≥ deg D + 1 − g` now — and recognize it is
  NOT enough for #1/#3.** Investigated per the task: the inequality alone does **not**
  discharge #1 or #3 (see §7). #3 (Abel sufficiency) needs the *equality* at `D = P+Q`
  to *produce* the third-kind/degree-1 function; #1 needs `l(P) = 2` (equality, `g=0`) to
  produce the degree-1 map to ℙ¹. Weak-RR is real, cheap content but it is a **dead leaf**
  for the two headline sorries — exactly the trap the repo already fell into with `deg_div`.
  *Do not* invest in weak-RR expecting it to unlock #1/#3.

- **(B) Isolate Riemann–Roch (equality form) as ONE named classical input** — a
  `structure`/typeclass `RiemannRochData X` or a single `theorem … := sorry` stated as
  Serre-dual RR `l(D) − l(K − D) = deg D + 1 − g` — and **derive #1 and #3 from it**. This
  is the honest, repo-consistent move (matches how the repo isolates `exists_cutSurface`,
  `MonodromyLiftFamily`, Abel). The *derivations* of #1/#3 from RR are themselves
  **multi-hundred to low-thousand LoC and gated on a complex-`ℙ¹` manifold shim that
  Mathlib entirely lacks** (§4, §7) — so even "isolate RR and derive" is not cheap.

- **(C) DO NOT prove RR from scratch.** Both honest from-scratch routes (Forster analytic
  §14–16, or scheme-theoretic) are **3k–8k+ LoC each on top of foundations Mathlib does not
  have** (no structure sheaf on a complex manifold; no coherent sheaves; no Dolbeault; no
  finiteness of `H¹`; no Serre duality; no complex `ℙ¹`). The abstract sheaf-cohomology
  machinery that *does* exist in Mathlib (`CategoryTheory.Sheaf.H`, snake lemma, Čech, Ext
  derived functors — all **[VERIFIED]** present) has **zero bridge** to the analytic
  category and would not shorten the analytic proof.

**Critical-path verdict.** The single hardest sub-theorem on any honest RR path is
**`H¹(X, O_D)` finite-dimensional + Serre duality `H¹(X,O_D) ≅ H⁰(X, Ω(−D))^*`** (Forster
§14 finiteness + §17 duality), whose engine is the **Dolbeault `∂̄`-solvability**
(Forster §13–§14, `H^{0,1}` / elliptic regularity) that Mathlib **completely lacks** and
that is the *same* Hodge nugget already flagged for #7 and Abel. There is no way to get the
RR *equality* (hence #1/#3) without paying this once.

**One-line recommendation:** *Isolate RR as a typeclass input `RiemannRochData` (equality,
Serre-dual form), add a minimal complex-`ℙ¹` shim (shared with #1), and derive #1/#3 as
conditional theorems — total derivation ~600–1200 LoC. Treat the inequality (weak-RR) as a
provable-but-non-load-bearing exercise (skip unless wanted for its own sake). Do not attempt
Dolbeault/Serre from scratch.*

---

## 1. Which Riemann–Roch — the exact statement for THIS repo

The repo is **analytic**: `genus X := Module.finrank ℂ (HolomorphicOneForms X)` where
`HolomorphicOneForms X` are global holomorphic 1-forms (`ContMDiffSection` of the
holomorphic cotangent bundle), `X` a compact connected complex 1-manifold
(`Genus.lean:34,66`). Divisors are `Divisor X := X →₀ ℤ` with `Divisor.deg = Finsupp.degree`
(`Abel.lean:67,71`). Meromorphic functions are the repo's own `MeromorphicFunction X`
(`Abel.lean:55`) with `MeromorphicFunction.divViaOrder` the divisor map (`Abel.lean:531`).
**[VERIFIED, repo]**

### 1.1 The cleanest Lean-formalizable statement (Serre-dual equality form)

Define the **complete linear system dimension** (Forster's `H⁰(X, O_D)`) directly in the
repo's vocabulary, with **no sheaf machinery**:

```text
L(D) := { f : MeromorphicFunction X // ∀ x, (D x) + f.orderAtPoint x ≥ 0 } ∪ {0}
        -- meromorphic f with div(f) ≥ −D, a ℂ-vector space
l(D) := finrank ℂ (L(D))
```

and the **canonical class** `K` = divisor of any nonzero meromorphic 1-form (well-defined up
to linear equivalence; `K x := ω.orderAtPoint x`). Then **Riemann–Roch (Forster Thm 16.9,
Serre-dual form)** is:

> **RR (target).** For a compact connected Riemann surface `X` of genus `g` and any divisor
> `D : Divisor X`:
> `l(D) − l(K − D) = Divisor.deg X D + 1 − g`. **[BOOK, Forster 16.9]**

This is the version to isolate. It is the cleanest because:
- It uses only objects the repo already has (`MeromorphicFunction`, `orderAtPoint`,
  `Divisor.deg`, `genus`); no `Sheaf`, no `Ext`, no cohomology types needed in the *statement*.
- `l(K − D) = dim H¹(X, O_D)` *by Serre duality* — so the duality is "baked into" the
  statement and the user never has to mention `H¹`.
- For the two consumers it specializes cleanly (§7):
  - `D = 0`: `l(0) − l(K) = 1 − g`, and `l(0) = 1` (only constants, by Liouville on a compact
    manifold — `MDifferentiable.exists_eq_const_of_compactSpace` **[VERIFIED]**), giving
    `l(K) = g`. (Sanity: `dim Ω(X) = g`.)
  - `D = P` (one point), `deg D = 1`: `l(P) − l(K − P) = 2 − g`. For `g = 0`, `K − P` has
    negative degree so `l(K−P)=0`, giving **`l(P) = 2`** — the non-constant function with one
    simple pole that yields the degree-1 map `X → ℙ¹` (#1).
  - `D = P + Q`, `deg D = 2`: `l(P+Q) − l(K−P−Q) = 3 − g`; combined with the third-kind
    1-form count this is Kleinerman's Lemma 4.1 `h⁰(Ω(P+Q)) = g + 1` (#3, Route B).

### 1.2 The weak (inequality) form

> **Weak-RR (Riemann inequality).** `l(D) ≥ deg D + 1 − g`. **[BOOK, Forster 16.5 corollary]**

Obtained from RR by dropping the `−l(K−D) ≤ 0` term. **Cheaper** (no Serre duality needed —
just the additivity χ-argument + `χ(0) ≥ 1 − g`, see §2), but **NOT sufficient for #1/#3**
(§7): both consumers need an *exact* dimension count (an equality / a lower bound that is
*also* an upper bound), which the inequality does not give.

### 1.3 Connection to the repo's encoding — what must be built to even *state* RR

Even the *statement* needs two repo-internal definitions that do **not yet exist**:
- `L(D)` as a `Submodule ℂ` (or a subtype with a `finrank`). The repo has `MeromorphicFunction`,
  `orderAtPoint`, and `divViaOrder` — so `L(D)` is definable, but the **finite-dimensionality
  of `L(D)`** is itself nontrivial (it is a *consequence* of RR / of `H¹` finiteness; for the
  statement one can use `Module.finrank` which is `0` on infinite-dim spaces, mirroring how
  `genus` is defined — `Genus.lean:60` docstring). **~80–150 LoC** to define `L`, `l`, `K`.
- `K` (canonical divisor): needs **existence of a nonzero global meromorphic 1-form**, which on
  a compact RS of any genus is *itself* a small RR/Dolbeault fact for `g=0` (ℙ¹ has the form
  `dz` only in a chart; the global meromorphic 1-form `dz` with a double pole at ∞ exists). For
  `g ≥ 1` a nonzero *holomorphic* 1-form exists (`genus ≥ 1`). Cleanest: **state RR with `K`
  as an explicit hypothesis** "given a canonical divisor `K`" rather than constructing it.

**Net for Q1:** the right statement is the **Serre-dual equality** `l(D) − l(K−D) = deg D + 1 − g`,
stated in the repo's `MeromorphicFunction`/`Divisor` language with `K` supplied as data. The
weak inequality is the cheap fallback but is non-load-bearing for the headline sorries.

---

## 2. The proof skeleton (Forster's analytic route, §14–16) with per-step availability

Forster *Lectures on Riemann Surfaces* (GTM 81) proves RR analytically via sheaf (Čech)
cohomology of the **structure sheaf `O` and the sheaves `O_D`** of meromorphic functions with
poles bounded by `D`. The chain (book theorem numbers; the repo PDF is the scanned image —
page offset +6):

| Step | Content (Forster) | Elementary? | Mathlib availability |
|---|---|---|---|
| (a) | **`H¹(X, O_D)` is finite-dimensional** (Forster **Thm 14.9**, "finiteness theorem"). Engine: the Čech `H¹` is computed on a finite cover; a Montel/compactness (Schwartz) argument shows the coboundary map is "almost surjective" ⟹ finite cokernel. | **No** — needs the finiteness theorem. | **ABSENT.** Mathlib has abstract `Sheaf.H` **[VERIFIED]** but **no** coherent-sheaf finiteness, no `O_D` sheaf, no Montel-for-sheaf-cohomology. **The repo's Montel** (`Jacobians/Montel.lean`, `HolomorphicOneForms.closedBall_isCompact`, `exists_convergent_subseq_of_bounded` **[VERIFIED present]**) is Montel for *global holomorphic 1-forms*, **not** the Čech-cochain Montel Forster 14.9 uses — related in spirit, not directly reusable. |
| (b) | **Skyscraper short exact sequence** `0 → O_D → O_{D+P} → ℂ_P → 0` (`ℂ_P` = skyscraper at `P`). Gives the long exact `0→H⁰(O_D)→H⁰(O_{D+P})→ℂ→H¹(O_D)→H¹(O_{D+P})→0`, so each `dim` jumps by ≤ 1 and `χ(D+P) = χ(D) + 1`. (Forster **§16.2–16.4**.) | **Yes**, *given* the cohomology functor + LES. | **Partial.** Mathlib HAS: skyscraper sheaves (`Mathlib/Topology/Sheaves/Skyscraper.lean`, `CategoryTheory/Sites/Point/Skyscraper.lean` **[VERIFIED]**), the snake lemma / homology long-exact-sequence (`ShortComplex.SnakeInput` **[VERIFIED]**, `Algebra/Homology/HomologySequence*`). MISSING: the sheaves `O_D` themselves and the SES *as sheaves on `X`* — there is **no `O_D` sheaf on a complex manifold** to feed the snake lemma. |
| (c) | **`χ(D) := dim H⁰(O_D) − dim H¹(O_D)` is additive**, so `χ(D) = deg D + χ(0)` by induction on `D` (add/remove points). (Forster **§16.5**.) | **Yes** — pure bookkeeping once (a),(b) hold. | **Partial.** The abstract Euler-characteristic additivity exists for graded ModuleCat (`HomologicalComplex.eulerChar` **[VERIFIED]**), and the induction is elementary `Finsupp` algebra (the repo's `Divisor.deg_add/_single` **[VERIFIED present]** are exactly the needed degree bookkeeping). |
| (d) | **`χ(0) = 1 − g`**: `H⁰(X, O) = ℂ` (constants, **Liouville**) and `dim H¹(X, O) = g` via **Serre duality `H¹(X,O) ≅ Ω(X)^*`** (Forster **§17.x**; equivalently the Dolbeault iso `H¹(X,O) ≅ H^{0,1}` + Hodge `≅ \overline{Ω(X)}`). | **`H⁰=ℂ` yes; `dim H¹=g` NO.** | `H⁰(O)=ℂ`: **HAVE** the Liouville input (`MDifferentiable.exists_eq_const_of_compactSpace` **[VERIFIED]**). `dim H¹(O)=g`: **ABSENT** — this is Serre duality / Dolbeault (§3), Mathlib's biggest gap here. |

**Reading of the table.** Steps **(b)** and **(c)** are *elementary given the cohomology
objects* and Mathlib has the abstract homological machinery to run them — **but** they
operate on `O_D`/`H^i(X, O_D)` which **do not exist in Mathlib for a complex manifold**.
Steps **(a)** (finiteness) and **(d)** (`dim H¹(O)=g`, i.e. Serre duality) are the **two hard
analytic inputs**, both ultimately resting on **Dolbeault `∂̄`-solvability** (Forster §13–14,
§17). So the analytic Forster route's "cheap middle" (b,c) is *unreachable* without first
building the sheaf-cohomology-of-a-complex-manifold layer from scratch — which is **larger
than building the two hard inputs directly**. This is why the from-scratch analytic route is
*not* recommended despite (b,c) looking easy.

**Map to Forster theorem numbers (for the steering log / REFERENCES.md):**
- finiteness `H¹(X, O_D) < ∞` = **Forster Thm 14.9**;
- skyscraper SES + `χ` additive = **Forster §16.2–16.5**;
- RR `χ(D) = deg D + 1 − g` = **Forster Thm 16.9**;
- Serre duality `H¹(X,O_D) ≅ H⁰(Ω(−D))^*` = **Forster §17** (uses §13 Dolbeault, §14
  finiteness, the residue pairing).

---

## 3. The Serre-duality / `∂̄` dependency — and the "RR without Serre duality" escape

RR's genuinely hard input is **`H¹(X, O_D) ≅ H⁰(X, Ω(−D))^*` (Serre duality)**, which Forster
(§17) builds from **(i) the Dolbeault lemma** (local `∂̄`-solvability: `∂̄u = f` solvable on a
disc, Forster §13), **(ii) the finiteness theorem** (§14), and **(iii) the residue pairing**
`H¹(X,O_D) × H⁰(Ω(−D)) → ℂ` via `(ξ, ω) ↦ ∑ residues`. **[BOOK]**

### 3.1 Can full Serre duality be avoided? — YES for the inequality, NO for #1/#3

**Forster's "RR without Serre duality" gives only the inequality.** Forster §16 actually
proves the **finiteness** and **additivity** (a)+(b)+(c) *first*, yielding
`χ(D) = deg D + χ(0)` and then **`χ(0) = 1 − g₁`** where `g₁ := dim H¹(X,O)` is a priori just
"some finite number" — the **arithmetic genus**. Without Serre duality one gets:

> **Weak-RR (Serre-free).** `l(D) ≥ χ(D) = deg D + 1 − g₁`, where `g₁ = dim H¹(X,O) < ∞`.
> **[BOOK, Forster §16 pre-§17]**

This is genuinely cheaper: it needs **(a) finiteness** (Dolbeault still, but only the
*finiteness* half, not the full duality iso/residue pairing) + **(b)+(c) elementary**. It
does **NOT** need the residue pairing or `g₁ = g` (= `dim Ω(X)`).

**But it is insufficient for THIS repo's consumers**, for two independent reasons:

1. **It bounds `l(D)` below by `deg D + 1 − g₁` with the *wrong* genus `g₁`.** The repo's
   `genus` is `g := dim Ω(X)` (the *geometric* genus). Identifying `g₁ = g` **is exactly
   Serre duality** (`H¹(X,O) ≅ Ω(X)^*`). Without it, weak-RR's bound is in terms of an
   uncomputed `g₁`, useless for a statement about `genus X`.

2. **#1 and #3 need an EQUALITY / matching upper bound, not a lower bound** (§7). E.g. #1
   needs `l(P) = 2` *exactly* when `g=0` to know the one-pole function is non-constant and has
   *degree exactly 1*; the inequality `l(P) ≥ 2` does give "non-constant function with a pole
   at `P`" but **not** that its only pole is the *single simple* pole at `P` (it could have
   `l(P) ≥ 2` from a function with worse poles if the upper bound fails) — the upper bound
   `l(K−P)=0` (negative degree ⟹ no sections) is the part that pins it, and that upper bound
   is the Serre-dual term. So even #1 needs the equality.

**Conclusion (Q3).** There IS an honest Serre-duality-avoiding route, but it yields only the
**inequality with the arithmetic genus `g₁`**, which is **a dead leaf** for #1/#3. To unlock
the headline sorries one must pay **either** the full Serre duality `H¹(X,O_D) ≅ H⁰(Ω(−D))^*`
(equality RR) **or**, at minimum, the identification `g₁ = g` (`H¹(X,O) ≅ Ω(X)^*`, the
`D=0` case of Serre duality) **plus** the negative-degree vanishing `deg E < 0 ⟹ l(E) = 0`
(elementary: a nonzero `f ∈ L(E)` has `div f ≥ −E`, so `0 = deg(div f) ≥ −deg E > 0`,
contradiction — but this needs **`deg(div f) = 0`** on a compact RS, which Mathlib/the repo
**lack** at manifold level, §4). The `deg(div f)=0` fact is itself a small residue-theorem /
argument-principle result Mathlib does not have.

**The irreducible nugget:** Dolbeault `∂̄`-solvability on a compact RS (Forster §13–14) — the
*same* Hodge gap already named for #7 (`docs/period_lattice_realbasis_research.md`: "Manifold
de Rham cohomology / Hodge theory: ABSENT, no open PR") and for Abel (`abel_riemannroch_research.md`
§2.1, Forster 19.10). **One Dolbeault layer would feed #7's Hodge variant, Abel Route A, and
RR simultaneously** — it is the true common denominator, ~1.5k–3k+ LoC with no Mathlib
scaffolding.

---

## 4. Mathlib inventory (VERIFIED this session at pin `8e3c989`)

### 4.1 HAVE — abstract homological / sheaf machinery (verified present)

| Capability | Mathlib name | Status |
|---|---|---|
| Abstract sheaf cohomology `H^n` of an abelian sheaf on any site (Ext-from-constant-sheaf def, Joël Riou 2024) | `CategoryTheory.Sheaf.H`, `Sheaf.cohomologyPresheaf` (`CategoryTheory/Sites/SheafCohomology/Basic.lean`) | **[VERIFIED]** `lean_run_code` typechecks `@CategoryTheory.Sheaf.H`. |
| Čech complex of a presheaf | `cechComplexFunctor`, `cochainComplexFunctor` (`SheafCohomology/Cech.lean`) | **[VERIFIED]** present (abstract). |
| Mayer–Vietoris for sheaf cohomology | `SheafCohomology/MayerVietoris.lean` | **[VERIFIED]** file present. |
| Nonabelian/`H¹` Čech (sheaves of groups) | `CategoryTheory/Sites/NonabelianCohomology/H1.lean` (`OneCocycle`, `OneCohomologyRelation`) | **[VERIFIED]** present. |
| Snake lemma / connecting hom in an abelian category | `CategoryTheory.ShortComplex.SnakeInput` (`Algebra/Homology/ShortComplex/SnakeLemma.lean`) | **[VERIFIED]** `lean_run_code` typechecks. |
| Homology long-exact-sequence from a SES of complexes | `Algebra/Homology/HomologySequence.lean`, `HomologySequenceLemmas.lean` | **[VERIFIED]** files present. |
| Euler characteristic of a graded/complex of `ModuleCat` + additivity | `HomologicalComplex.eulerChar`, `eulerChar_eq_sum_finSet…` (`Algebra/Homology/EulerCharacteristic.lean`) | **[VERIFIED]** `lean_run_code` typechecks `@HomologicalComplex.eulerChar`. |
| Skyscraper sheaf | `Mathlib/Topology/Sheaves/Skyscraper.lean`; `CategoryTheory/Sites/Point/Skyscraper.lean` | **[VERIFIED]** files present. |
| Right-derived functors / Ext | `CategoryTheory/Abelian/RightDerived.lean`, `Abelian/Ext.lean`; `DerivedCategory.Ext` | **[VERIFIED]** present (the `Sheaf.H` def is built on `Ext`). |

### 4.2 HAVE — analytic / repo-adjacent (verified)

| Capability | Mathlib name | Status |
|---|---|---|
| **Liouville on compact complex manifolds** (holomorphic ⟹ constant) — gives `H⁰(O)=ℂ` | `MDifferentiable.exists_eq_const_of_compactSpace`, `…apply_eq_of_compactSpace` (`Geometry/Manifold/Complex.lean`) | **[VERIFIED]** `lean_run_code` typechecks. |
| Planar meromorphic divisor + algebra | `MeromorphicOn.divisor`, `divisor_mul/_inv/_prod/_zpow` (`Analysis/Meromorphic/Divisor.lean`) | **[VERIFIED]** (`ℂ→E`, **planar only**). |
| Build planar meromorphic `f` from a finite divisor | `MeromorphicOn.extract_zeros_poles` (`Analysis/Meromorphic/FactorizedRational.lean`) | **[VERIFIED]** `lean_run_code` typechecks (**planar only**). |
| Single-residue Cauchy building block | `circleIntegral_sub_center_inv_smul_…_tendsto` → `2πi•y` | **[VERIFIED]** (the brick, **not** a residue theorem). |
| Box Cauchy / rectangle divergence | `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`; `MeasureTheory.…DivergenceTheorem` | **[VERIFIED]** (used by the repo's `CutSurface`/`GreenBox`). |

### 4.3 MISSING — the genuine absences (verified by exhaustive grep/run_code)

- **Riemann–Roch in any guise.** `grep -rln RiemannRoch` over all of Mathlib → **empty**;
  `leansearch "Riemann-Roch for curves"` → only Krull-dimension noise. **[VERIFIED]**
- **Serre duality (any form).** `grep -rln "SerreDuality\|Serre.*Duality"` → **empty**. **[VERIFIED]**
- **Dolbeault / `∂̄`-solvability / `H^{0,1}`.** No `Dolbeault`, no `dBar`; the only "dbar"
  hits are `ToAdditive`/`IntervalCases`/`CauchyIntegral` (false positives). **[VERIFIED]**
- **Coherent sheaves.** No coherent-sheaf theory; the 3 "coherent" hits
  (`SmallAffineZariski`, `IdealSheaf/Basic`, `Modules/Tilde`) are unrelated occurrences.
  **No finiteness theorem for cohomology** of any sheaf (proper/projective): grep empty.
  **[VERIFIED]**
- **Structure sheaf / `O_X` on a complex MANIFOLD.** `grep StructureSheaf` over
  `Geometry/Manifold` → **empty**. The sheaves `O_D` Forster's proof runs on **do not exist**.
  (Scheme `StructureSheaf` exists in `AlgebraicGeometry`, but the repo's `X` is a manifold, a
  different category — not connectible.) **[VERIFIED]**
- **Divisors on a curve / scheme; invertible sheaf `O(D)`; degree of a divisor on a curve.**
  No Weil/Cartier divisor (`find -iname "*Divisor*"` yields only the planar analytic file,
  ring-theoretic `ChainOfDivisors`, and number-theory `Divisors` — all unrelated). No
  `invertibleSheaf`/`O(D)`/Serre-twist. The only divisor-degree hit is
  `EllipticCurve/DivisionPolynomial/Degree` (polynomial degree, not divisor degree).
  **[VERIFIED]**
- **Complex `ℙ¹` / Riemann sphere as a manifold.** `Projectivization K V` exists as a bare
  type but has **no `TopologicalSpace`** instance, let alone `ChartedSpace ℂ` / `IsManifold`:
  `lean_run_code` `infer_instance` for `ChartedSpace ℂ (Projectivization ℂ (Fin 2 → ℂ))`
  **fails** ("failed to synthesize TopologicalSpace"). `AlgebraicGeometry.ProjectiveSpace`
  does not exist (unknown identifier). **No `Ω(ℙ¹)=0`, no `genus ℙ¹=0`.** **[VERIFIED]**
- **Residue theorem / argument principle / sum-of-residues = 0** on a compact RS, and
  **`deg(div f) = 0`** (every principal divisor has degree 0). No `residue` def in `Analysis`;
  no `argumentPrinciple`; "sum of residue" hits are number-theoretic residue classes mod `n`.
  **[VERIFIED]**

**Honest summary (Q4):** Mathlib has a **complete abstract homological-algebra + abstract
sheaf-cohomology toolkit** (snake lemma, LES, Čech, Ext, skyscraper, Euler char — all
verified) and the **`H⁰(O)=ℂ` Liouville input**. It has **none** of the analytic-geometry
bridge: no structure sheaf on a manifold, no coherent sheaves, no finiteness, no Serre
duality, no Dolbeault, no complex `ℙ¹`, no manifold residue/`deg(div)=0`. The abstract
toolkit is *necessary but radically insufficient*: there is nothing to *apply* the snake
lemma *to*.

---

## 5. Repo assets that transfer to an analytic RR proof

Verified by reading the repo this session.

| Asset (axiom-clean unless noted) | Location | Genuine input to RR? |
|---|---|---|
| **Montel's theorem** (for global holomorphic 1-forms) — `closedBall_isCompact`, `exists_convergent_subseq_of_bounded` | `Jacobians/Montel.lean` **[VERIFIED]** | **Partial / morally.** Forster's finiteness `H¹(X,O_D)<∞` (Thm 14.9) is a Montel/Schwartz compactness argument on *Čech cochains*. The repo's Montel is on `Ω(X)` (different space) — **the *technique* transfers, the *lemma* does not directly**. Still the closest existing scaffold for step (a). |
| `HolomorphicOneForms` / `genus` | `Genus.lean` | **Yes** — the RR statement is *about* these; `l(K)=g` is `dim Ω(X)` by definition. |
| **Liouville** wrapper usage (compact ⟹ const) | via `MDifferentiable.exists_eq_const_of_compactSpace` | **Yes** — gives `H⁰(X,O)=ℂ` = `l(0)=1`, step (d) easy half. |
| Line integrals on manifolds, `lineIntegral_pullback`, `pathSpeed_comp` | `LineIntegral.lean`, `TracePullback.lean` | **Indirect** — used by the period/Green stack below; not a direct RR input. |
| **Trace / pushforward of 1-forms** `traceForm`, `traceForm_comp`, `traceFormTotal` | `TraceForm.lean` **[VERIFIED present]** | **Tangential.** This is the engine of Abel *necessity* (Route A) and Riemann–Hurwitz, **not** RR. Does not feed RR or Serre duality. |
| **CutSurface / boundaryForm / Green** `cutSurface_R1/_R2`, `greenOnUnitBox`, `rectBoundaryIntegral`, `boundaryForm_eq_area`, `boundaryForm_pos` | `CutSurface*.lean`, `GreenBox.lean`, `GreenPositivity.lean`, `BoundaryPositivity.lean` **[VERIFIED present]** | **The most relevant transferable asset — for the residue pairing.** Serre duality's pairing `H¹(X,O_D) × H⁰(Ω(−D)) → ℂ` is `(ξ,ω) ↦ ∑ res(ξ·ω)`, and the **sum-of-residues = 0 / period bookkeeping is exactly the cut-surface + Green computation** the repo just built for R1/R2 (which are the *first/second* Riemann bilinear relations). The same `EdgeChangeOfVariables`/`boundaryForm`/box-Green toolkit is what a **reciprocity-law / residue-sum lemma** is built on. **So yes: the just-built #7 Green machinery is a genuine partial input to Serre's residue pairing** — but it is *infrastructure*, not the theorem; the Dolbeault half is still owed. |
| Branched-cover **degree layer** `ContMDiff.degree`, `degreeFiber`, `degreeFiber_eq_card_of_regularWitness` (degree well-definedness, ported brsanch) | `Jacobians/Discharge/Manifold/` **[VERIFIED present]** | **Yes, for the #1/#3 endgame** (degree-1 map ⟹ iso), *not* for RR itself. The "deg-1 cover ⟹ biholomorphism" step of #1/#3 reuses this. |
| Local meromorphic divisor (manifold-level `orderFun`, `divisor`, `zeros_finite`, `poles_finite`) | `Discharge/Manifold/MeromorphicDivisor.lean` **[VERIFIED present]** | **Yes** — the manifold-level order/divisor bookkeeping needed to *define* `L(D)` and to state `deg(div f)=0`. The repo already has finiteness of zeros/poles. |

**Answer to Q5's pointed question — "does the just-built period/Green machinery feed Serre
duality's residue pairing?"** **Yes, partially and genuinely:** the residue pairing's
*topological/integral* side (sum of residues = 0, the reciprocity bookkeeping) is the *same*
cut-surface + box-Green computation as R1/R2, so `CutSurface`/`boundaryForm`/`EdgeChangeOfVariables`
are the right tools and lower the marginal cost of the pairing. **But** the *analytic* side of
Serre duality (that the pairing is *perfect* / non-degenerate, i.e. `H¹ ≅ H⁰(Ω(−D))^*`) rests
on Dolbeault `∂̄`-solvability, which the Green machinery does **not** provide. So #7's assets
are a real but *partial* down-payment on Serre duality, not a discharge of it — exactly
mirroring the §6 finding in `abel_riemannroch_research.md` (#7 shares *infrastructure* with
Route B's reciprocity, not *logic*).

---

## 6. Keystone decomposition + LoC + critical path

Mirroring the period-lattice note's "~4–8 keystones with LoC". Three plans, in increasing cost.

### 6.1 Plan B (RECOMMENDED): isolate RR (equality), derive #1/#3 — provable-now portion

| # | Keystone | Content | LoC | Provable now? |
|---|---|---|---|---|
| B1 | `def L (D) : Submodule ℂ …`, `l D`, canonical `K` | linear system + dimension in repo's `MeromorphicFunction`/`orderAtPoint` language; `K` supplied as data | **80–150** | **Yes** (repo has all pieces). |
| B2 | `RiemannRochData X` (ISOLATED input) | the equality `l D − l (K−D) = deg D + 1 − g`, as a typeclass/structure or single `sorry` | **~20** (it *is* the isolated axiom) | n/a (isolated). |
| B3 | `complexProjectiveLine` shim (ISOLATED/built) | a complex-manifold `ℙ¹` with `genus ℙ¹ = 0`, `Ω(ℙ¹)=0` — **shared with #1** | **300–800** (if built minimally) **or ~50** (if also isolated) | **Partly** — `Projectivization` exists but needs a charted-space+`IsManifold` instance from scratch (**no Mathlib `ℙ¹` manifold**, §4). |
| B4 | `deg_div_eq_zero` | every principal divisor has degree 0 (needs manifold argument principle / sum-of-residues) | **400–900** | **No** (Mathlib/repo lack it; small residue-theorem build, the Green stack helps). |
| B5 | #1 derivation | `l(P)=2 ⟹` non-const 1-pole fn `⟹` deg-1 map `X→ℙ¹ ⟹` iso `⟹ X≃ₜ S²` (§7.1) | **300–600** | **Yes given B2,B3,B4** + repo degree layer + Liouville. |
| B6 | #3 derivation | `l(P+Q)=g+1 ⟹` third-kind `ω_{PQ} ⟹` Abel sufficiency endgame (§7.2) | **400–900** | **Partly** — needs B2 + the third-kind→Abel bridge (reciprocity, where the Green stack helps) + degree-1 endgame. |
| | **Plan B total (derivation only)** | | **~1.5k–3.3k LoC** on top of isolated RR + ℙ¹ | mixed |

**Single critical-path sub-theorem (within the "needs a big input" tier):** **`RiemannRochData`
itself** (B2), whose only honest discharge is **Serre duality + Dolbeault** (§3) — the
irreducible Hodge nugget. Within the *provable-now* tier, the binding constraint is **B3 (the
ℙ¹ complex-manifold shim)** — it is the gate for #1 and the shared blocker, and Mathlib has
**nothing** (no topology on `Projectivization`). **Recommendation: isolate B2 AND B3** (RR and
`ℙ¹`), prove B1/B4/B5/B6.

### 6.2 Plan A (weak-RR, provable now) — for completeness, NON-load-bearing

| # | Keystone | LoC | Provable now? |
|---|---|---|---|
| A1 | finiteness `H¹(X,O_D) < ∞` (Forster 14.9) | **1500–3000** | **No** — needs Dolbeault finiteness + an `O_D` sheaf on a manifold (absent). |
| A2 | skyscraper SES + LES + `χ` additive (Forster 16.2–16.5) | **400–800** | **Partly** — abstract snake/LES present, but no `O_D` sheaf to apply them to. |
| A3 | assemble `l(D) ≥ deg D + 1 − g₁` | **150–300** | Yes given A1,A2. |
| | **Plan A total** | **~2k–4k LoC** | **mostly absent** (A1 is the wall) |

**Plan A is NOT recommended**: it costs ~2–4k LoC, its hard half (A1) is the same Dolbeault
gap, and its output (inequality with arithmetic genus `g₁`) is a **dead leaf** for #1/#3 (§3).

### 6.3 Plan C (RR from scratch, equality) — scale only, DO NOT pursue

`Plan A (finiteness+χ)` + **Serre duality** (`+ Dolbeault §13 + residue pairing §17`,
**+1500–3000 LoC**, no scaffold) + **`O_D`-sheaf-on-a-manifold foundations** (the structure
sheaf, `O_D`, coherence — **+1000–2500 LoC**, entirely absent). **Total ~5k–9k+ LoC**,
dominated by foundations Mathlib refuses-to-have-yet. Strictly larger than #7 and Abel-from-
scratch combined.

### 6.4 What to isolate vs. prove (Q6 verdict)

- **Isolate** (repo-style, named classical theorem absent from Mathlib): **`RiemannRochData`**
  (equality, Serre-dual form) — and, pragmatically, the **`ℙ¹` complex-manifold shim** (or
  build it minimally; it is *also* needed by #1 independently).
- **Prove now** (reuses repo assets): `L/l/K` definitions (B1), `deg_div_eq_zero` (B4, the
  Green stack + manifold divisor layer help), and the #1/#3 derivations (B5/B6) modulo the
  ℙ¹ shim and the third-kind bridge.
- **Do NOT** attempt finiteness (A1), Dolbeault, or Serre duality from scratch — wrong
  cost/benefit; that is the one nugget to keep isolated.

---

## 7. Downstream payoff check — how RR discharges #1 and #3

### 7.1 #1 `genus_eq_zero_iff_homeo` (`Genus.lean:81`)

Target: `genus X = 0 ↔ Nonempty (X ≃ₜ Metric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1)`.
The `(⇐)` direction (`X ≃ₜ S² ⟹ genus 0`) is the easy topological half. The hard `(⇒)` is:

1. `genus X = 0`. Pick any `P : X`. Apply **RR equality** at `D = P`: `deg P = 1`, and
   `K − P` has `deg(K−P) = (2g−2) − 1 = −3 < 0` (for `g=0`), so `l(K−P) = 0` by **B4-style
   negative-degree vanishing**. Hence `l(P) = deg P + 1 − g + l(K−P) = 1 + 1 − 0 + 0 = 2`.
   **[BOOK, Forster 16.9 + the genus-0 computation]**
2. `l(P) = 2 > 1 = l(0)` ⟹ there is a **non-constant** meromorphic `f ∈ L(P)`, i.e. `f` has
   **a single simple pole at `P`** and no other poles. Such `f` is a holomorphic map
   `f : X → ℙ¹` of **degree 1** (one simple pole ⟹ generic fibre is a single point; uses the
   repo's `ContMDiff.degree`/`degreeFiber` layer + `deg(div f)=0`).
3. **Degree-1 holomorphic map of compact RS ⟹ biholomorphism** (injective by degree-1, open
   by open-mapping, hence homeomorphism; Liouville/`exists_eq_const_of_compactSpace` rules out
   degeneracy). So `X ≃ ℙ¹` biholomorphically, hence `X ≃ₜ ℙ¹ ≃ₜ S²`.
   **[BOOK, Forster §4.24 proper-map degree]**

**LoC for the #1 derivation:** **~300–600** (B5) *given* (i) RR equality (B2), (ii) the ℙ¹
shim with `ℙ¹ ≃ₜ S²` and `genus ℙ¹ = 0` (B3), (iii) `deg_div=0` (B4), (iv) the repo's degree
layer. **The ℙ¹ shim (B3) is the binding blocker** — without it step 2/3 cannot even be
stated. *Honest:* "RR discharges #1" is true only modulo the ℙ¹ manifold, which is a separate
~300–800 LoC build (or isolate).

### 7.2 #3 `abelJacobi_twoPoint_ne_zero` (`Abel.lean:666`)

Per `docs/abel_riemannroch_research.md` §2.2 (Route B), the repo consumes #3 via the
two-point divisor. RR's role is **Kleinerman Lemma 4.1**:

1. **RR equality** at `D = P + Q` (deg 2): `l(P+Q) − l(K−P−Q) = 2 + 1 − g = 3 − g`. The
   dual count on 1-forms gives `h⁰(Ω(P+Q)) = g + 1` (one extra 1-form beyond the `g`
   holomorphic ones) — a **third-kind differential `ω_{PQ}`** with simple poles at `P,Q`,
   residues `±1`. **[BOOK, Kleinerman Lemma 4.1, an RR+Serre computation]**
2. The **reciprocity law** `∫_{b_k} ω_{PQ} = 2πi ∫_Q^P ω_k` (Riemann's *third* bilinear
   relation) + period chasing ⟹ `abelJacobi(P−Q) = 0 ⟺ P−Q principal`. The reciprocity law
   is the **same cut-surface + Green computation** as R1/R2 (the repo's `CutSurface` stack) —
   a genuine reuse.
3. `P − Q` principal with `P ≠ Q` ⟹ degree-1 map ⟹ `g = 0`, contradicting `0 < genus X`
   (the §7.1 endgame, reusing the degree layer + ℙ¹ shim).

**LoC for the #3 derivation:** **~400–900** (B6) *given* RR equality (B2) + the reciprocity
lemma (new, built on the Green stack, ~300–600 of that) + the §7.1 endgame. **Alternatively**,
RR is *avoidable* for #3 via Forster Route A (Trace + Dolbeault, no RR) — but that pays the
Dolbeault gap instead (`abel_riemannroch_research.md` §2.1). **Net:** RR (Route B) discharges
#3, but only together with a reciprocity lemma and the same ℙ¹/degree endgame; it does **not**
make #3 cheap, and the deepest input (RR-equality ⟸ Serre/Dolbeault) is shared with #1.

**Confirmation of Q7 LoC:** the #1 and #3 *derivations from RR* are **~700–1500 LoC combined**
(B5+B6), realistic, **but gated on (a) the isolated RR equality, (b) a complex-`ℙ¹` manifold
shim, (c) `deg(div f)=0`, (d) a reciprocity lemma** — items (b),(c),(d) are themselves
hundreds of LoC and (b) is entirely absent from Mathlib. So "RR unlocks #1 and #3" is **true
in principle and the derivations are tractable, but each needs the ℙ¹ shim and a small
residue/reciprocity build on top of the isolated RR**.

---

## 8. Sources

**Primary (read this session / in repo):**
- **Otto Forster, *Lectures on Riemann Surfaces* (GTM 81)** — **§14** finiteness theorem
  (`H¹(X,O_D)<∞`, **Thm 14.9**); **§16** Riemann–Roch (skyscraper SES §16.2–16.4, `χ`
  additivity §16.5, **RR Thm 16.9** `l(D)−l(K−D)=deg D+1−g`, weak inequality 16.5 corollary);
  **§17** Serre duality (`H¹(X,O_D) ≅ H⁰(Ω(−D))^*` via §13 Dolbeault + residue pairing);
  §4.24 proper-map degree (deg-1 ⟹ iso); §20 Abel; §21 Jacobi inversion (RR used at 21.9).
  Repo PDF is a scanned image (page offset +6). **[BOOK]**
- **Seth Kleinerman, *The Jacobian, the Abel–Jacobi Map, and Abel's Theorem***
  (https://wstein.org/projects/kleinerman_99paper.pdf) — **Lemma 4.1** `h⁰(Ω(P+Q))=g+1` is a
  direct RR+Serre computation; **Lemma 4.2** reciprocity law; **Thm 4.3** Abel. The clean
  modern Route-B writeup. **[BOOK]**
- **Griffiths–Harris, *Principles of Algebraic Geometry*** (repo root PDF) — Ch.2 Riemann–Roch,
  Serre duality, residue pairing; third-kind differentials + reciprocity. **[BOOK]**
- **Miranda, *Algebraic Curves and Riemann Surfaces*** — Ch. VI–VII RR + Serre duality (the
  standard alternative reference). **[BELIEVED]**

**Repo (read this session):** `Jacobians/Genus.lean` (genus, `genus_eq_zero_iff_homeo`),
`Jacobians/Abel.lean` (`MeromorphicFunction`, `Divisor`, `orderAtPoint`, `divViaOrder`,
`twoPointDivisor`, `abelJacobi_twoPoint_ne_zero`), `Jacobians/Montel.lean` (Montel for `Ω(X)`),
`Jacobians/TraceForm.lean`, `Jacobians/CutSurface*.lean` + `GreenBox.lean`/`GreenPositivity.lean`/
`BoundaryPositivity.lean` (R1/R2, box-Green, residue-pairing infrastructure),
`Jacobians/Discharge/Manifold/{Degree,MeromorphicDivisor}.lean` (degree layer, manifold
divisor), `docs/{STATUS,abel_riemannroch_research,period_lattice_realbasis_research,REFERENCES}.md`.

**Mathlib (VERIFIED this session at pin `8e3c989`):**
- **Present (abstract):** `CategoryTheory.Sheaf.H` (sheaf cohomology, Ext-def),
  `SheafCohomology/{Cech,MayerVietoris}.lean`, `Sites/NonabelianCohomology/H1.lean`,
  `ShortComplex.SnakeInput` (snake lemma), `Algebra/Homology/HomologySequence*.lean` (LES),
  `HomologicalComplex.eulerChar` (Euler char), `Topology/Sheaves/Skyscraper.lean` +
  `Sites/Point/Skyscraper.lean`, `Abelian/{RightDerived,Ext}.lean` — all `lean_run_code`/grep
  confirmed.
- **Present (analytic):** `MDifferentiable.exists_eq_const_of_compactSpace` (Liouville/`H⁰=ℂ`),
  `MeromorphicOn.divisor` + `extract_zeros_poles` (**planar**), `circleIntegral_…_tendsto`
  (single-residue brick), `integral_boundary_rect_eq_zero…` / `DivergenceTheorem` (box Green).
- **ABSENT (grep/run_code empty):** Riemann–Roch (any form); Serre duality; Dolbeault/`∂̄`;
  coherent sheaves; finiteness of sheaf cohomology; structure sheaf `O_X`/`O_D` on a complex
  **manifold**; Weil/Cartier divisor / `O(D)` / divisor degree on a curve; complex `ℙ¹` /
  Riemann sphere manifold (`Projectivization` has no topology); residue theorem / argument
  principle / sum-of-residues=0 / `deg(div f)=0` on a compact RS.

**Status separation:** everything in §4.1–4.2 and the §4.3 absences is **[VERIFIED this
session]** against pin `8e3c989` via `lean_run_code`, `loogle`, `leansearch`, and source grep
of `/tmp/jacobian-brsanch/.lake/packages/mathlib/Mathlib` (same pin). The Forster/Kleinerman
theorem numbers and the proof skeleton are **[BOOK]**. The LoC estimates are **[BELIEVED]**
engineering judgement calibrated to the period-lattice (#7) and Abel notes.

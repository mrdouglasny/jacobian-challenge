# Serre §17 build plan — the actionable tower to `arithmeticGenus_eq_genus`

Grounded in a close reading of **Forster, *Lectures on Riemann Surfaces* (GTM 81), §17** (pp. 132–145),
cross-checked against the repo's existing infrastructure (2026-06-04). This is the *execution* companion
to `docs/hodge_bridge_research.md` (the route survey) — it records the **exact Forster theorem chain** and
maps each link to a concrete Lean obligation.

The headline `genus_eq_zero_iff_homeo` (forward) is gated on `arithmeticGenus_eq_genus : h1Dim 0 = genus X`.
Forster proves this as **§17.10 at `D = 0`**: `g = dim H¹(X,𝒪) = dim H⁰(X,Ω)`. Everything below is the
chain that establishes it. **Forster's §17 is entirely PDE-free** (no harmonic forms, no elliptic
regularity — those first appear in §19, which §16–17 never use). This confirms the repo's PDE-free route
and means **the `hodge_symmetry` (conjugation/L²) route is NOT needed**: Forster gives `g = h1Dim 0`
*directly* via the residue pairing.

## The Forster §17 theorem chain (verbatim structure)

| Forster | Statement | Repo status |
|---|---|---|
| **17.1** | `Res : H¹(X,Ω) → ℂ` via `H¹(X,Ω) ≅ ℰ^(2)/dℰ^(1,0)`, `Res(ξ)=(2πi)⁻¹∬_X ω` | ⛔ uses ∬_X (Stokes) — repo AVOIDS; use 17.2 instead |
| **17.2** | Mittag–Leffler distribution `μ=(ωᵢ)`, `δμ∈Z¹(Ω)`; `Res_a(μ):=Res_a(ωᵢ)`, `Res(μ):=∑_a Res_a(μ)` | ✅ local: `resAt`/`residueSum`/`formFnResidue` (Residue.lean, MittagLeffler.lean) |
| **17.3** | `Res(μ) = Res([δμ])` | ⚠ Forster proof = Stokes; repo needs only the **well-definedness** of `Res` on classes |
| **17.4** | `ω·: 𝒪_{D+K} ≅ Ω_D` (K = div ω); **Lemma**: `dim H⁰(Ω_D) ≥ deg D + k₀` from RR | 🔴 needs `Ω_D` space + RR ineq |
| **17.5** | pairing `⟨ω,ξ⟩ := Res(ωξ)`, `ι_D : H⁰(Ω_{−D}) → H¹(𝒪_D)*` | 🔴 needs the pairing assembly |
| **17.6** | `ι_D` **injective** (EASY) — local witness `η=(dz/z,0)`, `Res(ωη)=1` | 🟡 abstract core `finrank_le_of_injective_to_dual` ✅; witness `exists_formFnResidue_eq_one` ✅ |
| **17.7/17.8** | commuting squares; mult-by-ψ injective on duals | 🔴 bookkeeping, unbuilt |
| **17.9** | `ι_D` **surjective** (HARD) — the dimension-count pigeonhole + `ω₀=(1/ψ)ω` | 🟡 abstract core `serre_surjectivity_dim_core` ✅; instantiation 🔴 |
| **17.10/17.11** | `dim H¹(𝒪_D)=dim H⁰(Ω_{−D})`; **at D=0: `g = h1Dim 0 = dim H⁰(Ω)`** | ⟸ assembles 17.6+17.9 |

## The dependency tower (what actually gates `arithmeticGenus_eq_genus`)

```
arithmeticGenus_eq_genus  (= Forster 17.10 @ D=0)
  ├── 17.6 injective  (EASY: g ≤ h1Dim 0)
  │     ├── finrank_le_of_injective_to_dual ✅ (SerreDuality.lean)
  │     ├── residue-1 witness exists_formFnResidue_eq_one ✅ (FormCoeff.lean)
  │     └── the pairing ι₀  ──────────────────────┐
  └── 17.9 surjective (HARD: h1Dim 0 ≤ g)         │
        ├── serre_surjectivity_dim_core ✅ (SerreDuality.lean) — needs hΛ/hI/hV
        ├── hΛ,hV : Riemann–Roch dim estimates ───┤
        ├── hI    : 17.4 + 17.6 ───────────────────┤
        └── ω₀ = (1/ψ)ω  (a nonconstant merom. 1-form) ──┐
                                                          │
   THE TWO FOUNDATIONAL GATES (everything above bottoms out here):
   (A) global Res : H¹(X,Ω) → ℂ  WELL-DEFINED on classes        ⟸ 1-form residue theorem ∑Res(α)=0
   (B) Riemann–Roch (cohomological χ + finiteness)              ⟸ exists_cechModel (§14) + exists_skyscraperLES
   (C) the meromorphic-1-form space Ω_D (H⁰(Ω_{nP}))            ⟸ definitional build (unbuilt)
   (D) ω₀-existence (a nonconstant meromorphic function/1-form) ⟸ FALLS OUT of (B): RR ineq dim H⁰(𝒪_D)≥1−g+deg D≥2
```

**Key correction to earlier docs:** `ω₀`-existence is **not an independent unknown** — Forster 17.4 takes
`ω = df` for a nonconstant meromorphic `f`, and such `f` exists from the *cohomological* RR **inequality**
`dim H⁰(𝒪_D) ≥ 1−g+deg D` (≥2 for `deg D ≥ g+1`), which needs only finiteness (B), not Serre. So the tower
has exactly **two genuine foundational analytic gates: (A) the 1-form residue theorem, and (B) finiteness.**
Both are also needed by RR independently. There is **no third hidden wall** (no Hodge/elliptic).

## Gate (A): the 1-form residue theorem `∑_a Res_a(α) = 0`

This is what makes `Res` well-defined on `H¹(X,Ω)` classes (17.3 well-definedness, not the Stokes value).
Repo route = Miranda §VIII.3 trace-to-ℙ¹: `∑_X Res(α) = ∑_{ℙ¹} Res(Tr_F α) = 0`.
- ✅ **ℙ¹ residue theorem** `∑ Res + Res_∞ = 0` (`TraceResidue.lean`, `MeromorphicTrace:449`).
- ✅ **Lemma 3.2 simple-pole** `resAt_traceCoeff_of_simplePole` (`MeromorphicTrace`).
- ✅ The **df/f case fully assembled** structurally (`ResidueTheoremX.LogDerivTrace`) — but that is the
  W2/`deg_div` special case (simple poles only).
- 🔴 **GENERAL α (higher-order poles):** needs the *general* `resAt_traceCoeff` (residue change-of-variables
  under a branched sheet for order >1) — the one genuinely-new analytic atom here. Plus the branched cover
  `F = toRiemannSphere` of a chosen nonconstant `f` (from gate D), reusing the **W2 fibre machinery**
  (`ProperMapDegreeSheets` / `fibres_finite_statement_unconditional` / `LocalMultiplicitySheets`).
  ⇒ **Gate (A) is intertwined with W2 — finishing W2's fibre apparatus de-risks it.**

## Gate (B): finiteness + cohomological RR

- ✅ FA spine (Montel/Schwartz/`BddHol` compact-operator) — `Dolbeault/CechFiniteness*`, `Montel/*`.
- 🔴 `exists_cechModel` (manifold instantiation): chart-disk/subsingleton case done; **general Leray cover
  needs STEP B (refinement lift), ~1.5k LoC** — the hardest foundational piece.
- 🟡 `cohomological_riemannRoch` ⟸ `exists_skyscraperLES` (snake done; needs the 1-line chart-disk wire +
  H⁰-finiteness instance).

## Recommended build order (upstream → downstream, maximal reuse)

1. **Finish W2** (`exists_properMapDegree`, in progress) — closes `deg_div` AND hands gate (A) its fibre
   apparatus + a worked trace template.
2. **Gate (C): build the `Ω_D` meromorphic-1-form space** — definitional, ungated, the `MeromorphicFunction`
   analog for 1-forms. Needed by 17.4/17.5/17.9. *Startable now, in parallel; low risk.*
3. **Gate (A) general:** the general `resAt_traceCoeff` atom + assemble `∑Res(α)=0`, then descend
   `residueSum` to the well-defined global `Res : H¹(X,Ω)→ℂ` (MittagLeffler.lean plan).
4. **17.5 pairing + 17.6 EASY half** (`g ≤ h1Dim 0`): wire `Res` + `exists_formFnResidue_eq_one` into
   `ι₀`, feed `finrank_le_of_injective_to_dual`. *First genuinely-Serre sorry-free result.*
5. **Gate (B): finiteness** (`exists_cechModel` general / STEP B) + `exists_skyscraperLES` wire ⇒
   cohomological RR ⇒ the `hΛ/hI/hV` dim estimates.
6. **17.9 HARD half:** instantiate `serre_surjectivity_dim_core` with the cohomology objects + (5) ⇒
   `ι_D` surjective ⇒ **17.10 @ D=0 ⇒ `arithmeticGenus_eq_genus`** ⇒ headline forward.

**Honest scope:** steps 2–6 are a multi-session build (~3–5k LoC across the residue theorem, `Ω_D`, the
pairing, finiteness STEP B, and the §17 assembly). The abstract cores (steps' linear-algebra hearts) and
the local residue calculus are already proven; the residual is the geometric/analytic instantiation. **No
hidden Hodge/elliptic wall** — the scariest scenario is ruled out (Forster §16–17 are PDE-free).

## References
- Forster, *Lectures on Riemann Surfaces*, GTM 81, §17.1–17.11 (Serre duality), §16 (Riemann–Roch),
  §14 (finiteness). Local PDFs in repo root.
- Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (trace `Tr_F`, Lemma 3.2, ℙ¹ residue theorem).

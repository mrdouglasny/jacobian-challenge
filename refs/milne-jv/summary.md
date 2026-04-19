# Milne — Jacobian Varieties (JV)

**Citation.** J. S. Milne, "Jacobian Varieties," original TeX of Chapter VII of *Arithmetic Geometry* (Storrs, Conn., 1984), Springer 1986, pp. 167–212. Version dated 12 June 2021 (TOC restored, corrections, index, asides added).

**URL.** https://www.jmilne.org/math/xnotes/JVs.pdf (freely available).

**Scope.** Detailed treatment of Jacobian varieties of complete nonsingular curves over a field. Companion to Milne's "Abelian Varieties" notes. 14 sections (~48 pages + bibliography + index).

## Structure

| § | Topic | Note |
|---|-------|------|
| 1 | Definitions (via `Pic⁰` functor) | Key for our formalization |
| 2 | Canonical maps from `C` to its Jacobian | Abel-Jacobi |
| 3 | Symmetric powers of a curve | `C^(r)` = `Sym^r C` |
| 4 | Construction of the Jacobian variety | Main existence proof |
| 5 | Canonical maps from symmetric powers | `C^(r) → J(C)` |
| 6 | Jacobian as Albanese; autoduality | `J(C) ≃ J(C)^∨` |
| 7 | Weil's construction of the Jacobian | Alternative construction |
| 8 | Generalizations | Singular curves, generalized Jacobians |
| 9 | Obtaining coverings of a curve from its Jacobian | |
| 10 | Abelian varieties are quotients of Jacobian varieties | |
| 11 | The zeta function of a curve | |
| 12 | Torelli's theorem: statement and applications | |
| 13 | Torelli's theorem: the proof | |
| 14 | Bibliographic notes | |

## Relevance to the Jacobian challenge

**Very strong for the algebraic-geometry construction** (Approach B from our `docs/plan.md`). Milne §1 defines the Jacobian as an abelian variety representing the functor `T ↦ P_C^0(T) = {L ∈ Pic(C × T) | deg L_t = 0 for all t} / q* Pic(T)`. Existence (Theorem 1.1) is proved in §4; when `C` has a `k`-rational point `P`, the characterization takes the attractive form of a "divisorial correspondence" (Theorem 1.2).

**Relevance to Buzzard's API.**

- `Jacobian X` : corresponds to Milne's `J(C)`.
- `Jacobian.ofCurve P : X → Jacobian X` : Milne's canonical map `C → J(C)` (§2); one for each rational point.
- `ofCurve_inj` (`g > 0` ⇒ injective) : follows from the discussion in §2, where `C → J` is shown to be a closed immersion when `g ≥ 1`.
- `Jacobian.pushforward` / `pullback` : functoriality of `Pic⁰`; §10 on quotients by morphisms.
- `pushforward_pullback = deg • id` : for `f : C → C'` finite of degree `d`, `f_* f^*` on `Pic⁰` equals multiplication by `d` — this IS the motivating identity and is classical.

**Caveat for our setting.** Milne works with schemes over a field, not compact Riemann surfaces. The bridge is GAGA (analytic ↔ algebraic categories coincide for compact complex manifolds), which is not in Mathlib. So Milne's proofs don't port directly, but the *structural story* (what needs to be true, how the proofs go) is the same.

## Recommended reading order for Phase C planning

1. §1 Definitions — understand the functor-of-points characterization
2. §2 Canonical maps — the Abel-Jacobi map and `ofCurve_inj`
3. §4 Construction — the hard part: existence. Weil's alternative (§7) may be more concrete.
4. §6 Autoduality — how the principal polarization enters; needed for theta functions

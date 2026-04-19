# Milne — Abelian Varieties (AV)

**Citation.** J. S. Milne, "Abelian Varieties," original TeX of Chapter V of *Arithmetic Geometry* (Storrs, Conn., 1984), Springer 1986, pp. 103–150. Version dated 2 January 2022 (TOC restored, corrections, index added; numbering unchanged).

**URL.** https://www.jmilne.org/math/xnotes/AVs.pdf (freely available).

**Scope.** Algebraic treatment of abelian varieties over an arbitrary base field. Follows Mumford's 1970 book but most results are stated relative to an arbitrary base field, with proofs frequently omitted or sketched. 20 sections (~47 pages + bibliography + index).

## Structure

| § | Topic |
|---|-------|
| 1 | Definitions (group variety, abelian variety) |
| 2 | Rigidity |
| 3 | Rational maps into abelian varieties |
| 4 | Review of cohomology of schemes |
| 5 | The seesaw principle |
| 6 | Theorems of the cube and the square |
| 7 | Abelian varieties are projective |
| 8 | Isogenies |
| 9 | The dual abelian variety: definition |
| 10 | The dual abelian variety: construction |
| 11 | The dual exact sequence |
| 12 | Endomorphisms |
| 13 | Polarizations and cohomology of invertible sheaves |
| 14 | A finiteness theorem |
| 15 | Étale cohomology of an abelian variety |
| 16 | Pairings |
| 17 | The Rosati involution |
| 18 | Two more finiteness theorems |
| 19 | The zeta function of an abelian variety |
| 20 | Abelian schemes |

## Relevance to the Jacobian challenge

**Strong** for the abstract abelian-variety side (dual, polarizations, isogenies, Rosati involution) — these are exactly the structures needed on `Jacobian X` once you have it as a ℂ^g / Λ torus with a polarization from the period pairing.

**Weak** for the complex-analytic / theta-function side — this is an arithmetic-geometry-flavored text; complex-analytic constructions (Riemann bilinear relations, explicit theta series) are referenced rather than developed.

Best used as: reference for the functorial / structural properties `Jacobian.pushforward`, `Jacobian.pullback` must satisfy, and for the definition / cohomological interpretation of `Pic⁰`.

## Conventions (relevant to formalization)

- Assumes reader familiar with Hartshorne II, III + some étale cohomology.
- Variety means separated scheme of finite type, geometrically integral.
- Divisors are Cartier (= Weil on nonsingular).
- Ground field fixed per statement — sheaf of `π : W → V` a map of `k`-varieties is implicitly over `k`.

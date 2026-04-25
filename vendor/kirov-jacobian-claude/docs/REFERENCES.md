# References — Jacobians Lean API

Canonical sources for every non-trivial construction and theorem in this
project. Policy: open the **primary** first. If insufficient, check the
**secondary**. Escalate to **specialist** sources only when primaries
disagree or are too terse. Record the consulted source in commit messages
and in comments above difficult proofs.

## Primary pair (cover the whole challenge)

- **Otto Forster.** *Lectures on Riemann Surfaces.* GTM 81, Springer,
  1981 (reprinted 1991).
  [Springer page](https://link.springer.com/book/10.1007/978-1-4612-5961-9).
  Analytic, rigorous, self-contained. Our default. Use as the source of
  truth unless explicitly overridden below.

- **Rick Miranda.** *Algebraic Curves and Riemann Surfaces.* AMS GSM 5,
  1995. [AMS page](https://bookstore.ams.org/gsm-5/). Accessible bridge
  between analytic and algebraic viewpoints; use when Forster's style is
  too terse or when a divisor-theoretic perspective clarifies things.

## Per-sorry canonical references

Record chapter/section pointers next to each sorry as it's closed.

| Sorry | Primary | Secondary |
|---|---|---|
| `genus X` | Forster §14 (topological genus) | Miranda Ch. IV §1 |
| `genus_eq_zero_iff_homeo` | Forster §27 (uniformization genus 0) | Donaldson, *Riemann Surfaces* |
| `Jacobian X` (definition) | Forster §20–21 (periods, Jacobian) | Miranda Ch. VIII §§1–2 |
| `Jacobian` instances (65–86) | Forster §21 (Jacobian is a torus) | Lee, *Smooth Manifolds*, Ch. 21 |
| `ofCurve` (Abel–Jacobi map) | Forster §20 | Miranda Ch. VIII §1 |
| `ofCurve_contMDiff` | Forster §21 (holomorphicity) | Miranda Ch. VIII §2 |
| `ofCurve_self` | trivial (definition unwinding) | — |
| `ofCurve_inj` (Abel's theorem) | Forster §21 | Miranda Ch. VIII §3 |
| `pushforward`, `pullback` | Miranda Ch. VII | Griffiths–Harris Ch. 2 |
| `pushforward_contMDiff`, `pullback_contMDiff` | Miranda Ch. VII | — |
| `pushforward_id_apply`, `pushforward_comp_apply`, mirror for pullback | trivial (functoriality) | — |
| `ContMDiff.degree` | Forster §4 (proper holom. maps) | Miranda Ch. IV |
| `pushforward_pullback = deg` | Miranda Ch. VIII §3 | Griffiths–Harris §2.7; Bost (below) |

## Specialist / backup

Use when the primary is opaque or incomplete on a specific point.

- **Phillip Griffiths & Joseph Harris.** *Principles of Algebraic
  Geometry.* Wiley, 1978. Ch. 2 is the classic dense reference for
  Riemann surfaces; Ch. 2 §7 is the go-to for Jacobian functoriality and
  `push ∘ pull = deg`.
- **Hershel Farkas & Irwin Kra.** *Riemann Surfaces.* GTM 71. Exhaustive
  on the period matrix, Riemann bilinear relations, theta functions.
  Use when you need the full-rank / positive-definite lattice argument
  in detail.
- **Dror Varolin.** *Riemann Surfaces by Way of Complex Analysis.* AMS
  GSM 125, 2011. Modern line-bundle perspective; useful for the Pic⁰ ↔
  analytic Jacobian correspondence (future work, not closure of current
  sorries).
  [AMS page](https://www.ams.org/books/gsm/125/).
- **Jean-Benoît Bost.** *Introduction to Compact Riemann Surfaces,
  Jacobians, and Abelian Varieties.* In *From Number Theory to Physics*,
  Springer, 1992.
  [Chapter PDF](https://link.springer.com/content/pdf/10.1007/978-3-662-02838-4_2.pdf).
  Historical motivation; good for framing.
- **Simon Donaldson.** *Riemann Surfaces.* Oxford, 2011. Includes
  uniformization with a modern PDE flavour — useful for
  `genus_eq_zero_iff_homeo` specifically.
- **Jürgen Jost.** *Compact Riemann Surfaces.* Springer, 2006. Another
  uniformization source (variational / Dirichlet principle).

## Topology prerequisites (H₁, Euler char, closed surfaces)

- **Allen Hatcher.** *Algebraic Topology.* Cambridge, 2002. Free PDF at
  [pi.math.cornell.edu/~hatcher/AT/ATpage.html](https://pi.math.cornell.edu/~hatcher/AT/ATpage.html).
  Ch. 2 for singular H₁ (Hurewicz in §2.A). §2.2 for CW-complex Euler
  characteristic. Definitive for the topological genus story.

## Smooth-manifold / Lie-group prerequisites

- **John M. Lee.** *Introduction to Smooth Manifolds.* GTM 218, 2nd ed.,
  Springer, 2013. Ch. 7–8 (Lie groups); Ch. 21 (Lie subgroups, quotients).
  Source for the "quotient of a f.d. Lie group by a discrete closed
  subgroup is a Lie group" lemma that we'll upstream to Mathlib.

## Formalization context

Not proofs — pointers to Lean / Mathlib infrastructure and related work.

- **Mathlib4 docs** at commit 8e3c989: browse locally via
  `.lake/packages/mathlib/Mathlib/`. Key directories for this project:
  - `Geometry/Manifold/` — charted spaces, `IsManifold`, `ContMDiff`,
    `LieGroup`, complex manifolds, sheaves.
  - `Algebra/Module/ZLattice/` — lattices we'll quotient by.
  - `AlgebraicTopology/SingularHomology/` — singular H₁ via functor.
  - `CategoryTheory/Sites/SheafCohomology/` — sheaf cohomology via Ext.
  - `Analysis/Calculus/DifferentialForm/Basic.lean` — exterior
    derivative on normed spaces.
- [Rothgang, *Differential Geometry in Lean* (Potsdam 2025)](https://www.math.uni-bonn.de/people/rothgang/slides_Potsdam2025.pdf).
- [Sam Lindauer, MSc thesis, *Formalising Differential Geometry and
  Topology in Lean*](https://studenttheses.uu.nl/bitstream/handle/20.500.12932/49043/MSc.%20Thesis,%20Sam%20Lindauer,%20Mathematical%20Sciences.pdf).
- [Floris van Doorn et al., *Elements of Differential Geometry in Lean*
  (arXiv 2108.00484)](https://arxiv.org/pdf/2108.00484).
- [Seth Kleinerman, *The Jacobian, the Abel–Jacobi Map, and Abel's
  Theorem* (expository)](https://wstein.org/projects/kleinerman_99paper.pdf)
  — short, readable, useful cross-check for definitions.

## Learning from scratch (for the non-mathematician collaborator)

If the user's background is roughly *Tao, Analysis I* — i.e. rigorous real
analysis but no complex analysis, no topology, no algebra beyond groups —
the ladder to reading Kleinerman looks like this.

**Instant intuition pass (~1–2 hours; no textbook needed):**

- Wikipedia: [Riemann surface](https://en.wikipedia.org/wiki/Riemann_surface).
- Wikipedia: [Genus (mathematics)](https://en.wikipedia.org/wiki/Genus_(mathematics)).
- Wikipedia: [Divisor (algebraic geometry)](https://en.wikipedia.org/wiki/Divisor_(algebraic_geometry)).

After this the user can follow the *shape* of the formalization and
spot-check definitions, but not proofs.

**Real understanding (unavoidable): complex analysis first.**

- **Stein & Shakarchi, *Complex Analysis*** (Princeton Lectures II),
  Chapters 1–3. ~100 pages to Cauchy's theorem and residues.
- Alternative if more comfortable in the same style as Tao I: Tao's own
  *Analysis II* (2nd ed), complex-analysis chapter.

**Riemann surfaces on top of that:**

- **Miranda**, Chapters 1 (Riemann surface definitions + examples), 5
  §1 (divisors), 6 (holomorphic 1-forms), 8 (Jacobian + Abel).
- Alternative, free PDF lecture notes:
  [McMullen, Harvard Math 213b](https://people.math.harvard.edu/~ctm/papers/home/text/class/harvard/213b/course/course.pdf).

## Workflow

- When opening a new sorry to close, open the primary source at the
  relevant section and write a short `-- Following <source> §X.Y` comment
  above the proof.
- If the primary is unhelpful, cross-check against the secondary,
  document which one drove the formalization.
- On upstreaming to Mathlib, cite the primary in the file-level
  docstring.

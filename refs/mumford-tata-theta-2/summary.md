# Mumford — Tata Lectures on Theta II

**Citation.** David Mumford, with the collaboration of C. Musili, M. Nori, E. Previato, M. Stillman, and H. Umemura, *Tata Lectures on Theta II: Jacobian Theta Functions and Differential Equations*, Progress in Mathematics 43, Birkhäuser Boston, 1984 (original); reprinted as Modern Birkhäuser Classics. ISBN 0-8176-3110-0 (print) / 978-0-8176-4578-6 (Birkhäuser reprint).

**Provenance.** Obtained via Harvard institutional Springer access; stored in this repo under `refs/mumford-tata-theta-2/TataTheta2.pdf` for research use.

**Approach.** Vol II is Chapter III of the four-chapter theta plan. It restricts to **Jacobian theta functions** — i.e., the case when the period matrix `Ω` comes from a compact Riemann surface rather than an arbitrary symmetric matrix in the Siegel upper half space. Two motivating questions: (i) what extra function-theoretic identities do Jacobian `ϑ` satisfy, and (ii) how do these identities produce solutions of classical nonlinear PDEs (KdV, KP, Sine-Gordon)?

## Structure (from TOC)

**Chapter IIIa — Elementary Construction of Hyperelliptic Jacobians** (§§0–11, ~200 pp).

§0 reviews algebraic geometry (makes the book self-contained for analysts). §§1–4 work concretely on hyperelliptic curves: divisors, algebraic construction of `Jac(C)`, translation-invariant vector fields, Neumann's integrable dynamical system.

**§5 "Tying together the analytic Jacobian and algebraic Jacobian"** (p. 3.75) — the explicit GAGA-style equivalence for Jacobians in the hyperelliptic case. **This is the single most relevant section in Vol II for our formalization**: it shows concretely how the analytic Jacobian `ℂ^g/Λ_Ω` built from theta functions (Vol I §II.2) matches the algebraic Jacobian `Pic⁰(C)` built from divisor classes (Milne JV) in the hyperelliptic setting.

§§6–11 then continue: theta characteristics and Riemann's fundamental vanishing property; Frobenius' theta formula; Thomae's formula and moduli of hyperelliptic curves; characterization of hyperelliptic period matrices; the hyperelliptic `℘`-function; the KdV hierarchy.

**Chapter IIIb — Fay's Trisecant Identity** (§§1–5, ~40 pp).

§1 defines the prime form `E(x, y)` on a Riemann surface. §2 Fay's trisecant identity. §3 corollaries. §4 applications to differential equations. §5 generalized Jacobian of a singular curve and solutions.

**Chapter IIIc — Resolutions of Algebraic Equations by Theta Constants** (Umemura, ~10 pp).

Appendix by H. Umemura: solving algebraic equations of arbitrary degree using hyperelliptic theta functions + hyperelliptic integrals, extending Hermite–Kronecker (degree 5 via elliptic modular functions).

## Relevance to the Jacobian challenge

**Highly relevant for two specific things, mostly orthogonal to Buzzard's sorries:**

1. **§IIIa.5 (analytic ↔ algebraic Jacobian)** is the explicit bridge we need if we ever want to prove that the period-lattice Jacobian (Vol I construction) equals Pic⁰ (Milne JV construction). Buzzard's challenge doesn't require proving this equivalence, but it's exactly the kind of "real challenge" Buzzard mentions in the Zulip thread: "Of course the real challenge would be to prove that the Jacobian is all three of these definitions." §IIIa.5 gives the hyperelliptic case of this bridge — a natural first formalization target.

2. **§IIIb.1 (prime form `E(x, y)`)** and Fay's identity are the modern-classical tools for `pushforward`/`pullback` identities between Jacobians. If closing `pushforward_pullback = deg • id` via theta-function manipulation is the chosen strategy, Fay's identity is the clean way to do it.

**Largely beyond Buzzard's scope:**

§§6–11 of IIIa (theta vanishing, Thomae, KdV) and most of IIIb (PDE applications) are about Jacobian theta functions as mathematical objects in their own right, not about the abstract `Jacobian X`-as-a-type construction that Buzzard's challenge is after. These sections are **of substantial independent interest for your physics work** (KdV hierarchy, integrable systems, generalized Jacobians of singular curves, tau functions) but do not feed into the 22 sorries directly.

## Recommended triage for our project

- **Read §IIIa.5** (~20 pages) when we need the analytic-↔-algebraic bridge or want a hyperelliptic sanity-check construction.
- **Read §IIIb.1–2** (~15 pages) if Fay's identity becomes the natural tool for `pushforward_pullback`.
- **Defer §§6–11 of IIIa** and §§3–5 of IIIb to a separate "integrable systems / KdV via Jacobians" subproject. Not on the critical path for the challenge.

## What's still missing

Vol II adds algebraic geometry (schemes appear from §IIIa.0 onward) but still does not cover: the Heisenberg-Weil representation interpretation of theta, nor theta functions for abelian varieties over arbitrary fields. Those are in Vol III (Chapter IV).

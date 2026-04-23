# Buzzard's Jacobian Challenge — summary

Posted 19 April 2026 by Kevin Buzzard to the Lean Zulip (stream `#Autoformalization`, topic `Jacobian challenge`). Canonical URL: https://tinyurl.com/JacobianChallenge, gist `kbuzzard/778bc714030b3e974ab5f4038783d1a9`. Version v0.2 as of the scaffolding of this repo. Thread spans 2026-04-19 through 2026-04-23 (53 messages at the time this file was written).

## The challenge

A single Lean file pinned to Mathlib commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026). `Jacobians/Challenge.lean` in this repo is a verbatim copy.

### Data sorries (defs and instances)

- `genus X : ℕ`
- `Jacobian X : Type u`
- `AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace (Fin (genus X) → ℂ)`, `IsManifold`, `LieAddGroup` instances on `Jacobian X`
- `Jacobian.ofCurve : X → X → Jacobian X` — the Abel-Jacobi map
- `ContMDiff.degree` — degree of a holomorphic map between compact Riemann surfaces
- `Jacobian.pushforward`, `Jacobian.pullback` — continuous additive morphisms

### Prop sorries (theorems)

- `genus_eq_zero_iff_homeo` — genus 0 ↔ homeomorphic to the 2-sphere (blocks the `Jacobian := 0` hack)
- `ofCurve_self`, `ofCurve_inj` — the second forces Abel-Jacobi to be genuinely injective in positive genus
- Holomorphicity: `ofCurve_contMDiff`, `pushforward_contMDiff`, `pullback_contMDiff`
- Functoriality: `pushforward_id_apply`, `pushforward_comp_apply`, `pullback_id_apply`, `pullback_comp_apply`
- `pushforward_pullback`: `f_* ∘ f^* = deg(f) • id` — the key nontrivial identity

### Why this shape

Buzzard explicitly designed the API to prevent hack answers. Defining `Jacobian := 0` satisfies the type signatures and many of the functorial lemmas, but `ofCurve_inj` forces the Abel-Jacobi map to be injective in positive genus, and `genus_eq_zero_iff_homeo` forces `genus` to track the actual topology of the surface. The two combined close the hack gap.

Buzzard's own sketch of how the constraints bite (2026-04-19): "Let X be a compact Riemann surface of actual genus 2 or more. It's not homeomorphic to the sphere so a sorry in the file forces X to have AI genus at least 1. Now to fill in other sorries we have to come up with an injective holomorphic map from X to a compact connected Lie group of AI dimension at least 1 and it seemed to me that already asking this is asking a nontrivial thing, whether it's the Jacobian or not; in fact I suspect that the Jacobian is the easiest example!"

## Buzzard's framing

- Everything was known by the 1850s (Abel 1829, Jacobi 1851).
- "This challenge is to solve something which humans did nearly 200 years ago. Note that autoformalization of FLT will involve having to solve challenges which are 100x as difficult as this."
- Real motivation: is AI useful for Mathlib? The Jacobian of a compact Riemann surface appears in recent top-journal papers whose *statements* are not even expressible in current Mathlib. A clean AI-produced definition + sufficient API could be PR'd (just the definition and basic API); the remaining AI proofs can live in `merely-true` or similar.
- On anti-AI sentiment among reviewers: "Mathlib reviewers who are being faced with a deluge of ok-but-needs-work PRs from AIs and the reviewers have finally thrown up their hands and said 'this is pointless, I don't want to explain to an AI why their PR is mediocre because they will not learn so I am not motivated to put in the effort'."
- Why Riemann surfaces, not algebraic geometry: "(a) I wanted an excuse to learn something about how differential geometry is done in mathlib and (b) I was not sure yet how much dimension theory we had in algebraic geometry but I knew how to say 'let X be a d-dimensional manifold' in differential geometry. The Jacobian is universal for maps from curves into abelian varieties but we don't have abelian varieties in alg geom either. Oh and (c) the Annals paper had Jacobian of a compact Riemann surface."
- Kevin has **no private solution**: "No! Absolutely not! This is months of work!"
- Kevin is **not himself** a diff-geom/real-analysis expert: "I am not at all an expert in the real analysis part of the library and I thank those who responded to all my questions in the thread #mathlib4 > Basic compact Riemann surface questions which came up when I was trying to write the code!"
- Bigger picture: "Remember that there are 1000 of these, some much harder than this one, before we can even say that we can state what is going on in mathematics in 2026, let alone start to consider formalising the proofs."

## Core mathematical obstruction

Kevin (2026-04-19): "All definitions of Jacobian that I know involve quotienting a manifold by a discrete group, which isn't in mathlib as far as I know." Two routes:

1. **Symmetric product `X^g / S_g`**: "involves a delicate local analysis when points coincide."
2. **Dual of holomorphic 1-forms / H₁**: "will involve integrating differentials around loops which we don't have either, at least in this generality."

On the H₁ route specifically: "another issue will be proving that an element of H_1(ℤ) gives a well-defined linear map on 1-forms ('integrate me'), which feels like something which Math Inc made progress on in the special case where the Riemann surface was the complex numbers in their autoformalization of Viazovska; indeed this was at the back of my mind when I was thinking about the reasonableness of this challenge. My guess is that going from integrals on ℂ to integrals on a Riemann surface (which locally looks like ℂ) will be an interesting challenge."

Michael Rothgang (2026-04-19): manifold-quotient-by-discrete-group work is actively in progress — "the charted space instance is awaiting review (I've mentored it, so cannot approve it); a definition 'smooth Lie group action on a manifold' is missing (which is not hard); modulo that, the manifold instance is sorry-free and just needs clean-up." Dominic Steinitz (2026-04-22) pointed to his own draft in `Mathlib/Geometry/Manifold/Algebra/PrincipalGBundle.lean` and Mathlib PR #38374.

Kevin on the three strategies Claude suggested (see below): "For the first one, one piece of hard work is writing down the map from Lambda to C^g (integrating differential forms on a manifold). For the second one, the hard part is putting a complex manifold structure on the group (will need Riemann-Roch and more). For the third one (and maybe for all of them) one issue will be proving that the spaces are finite-dimensional (maybe needs Serre duality). Of course the real challenge would be to prove that the Jacobian is all three of these definitions; this is what mathlib would really want. But it is hard work to even write down some of these definitions."

## Idiomatic fixes (folded into v0.2)

Sébastien Gouëzel:
- `Type*` over `Type u` (Kevin: "I wanted to ensure that the Jacobian lived in the same universe as the curve, but most universes can be removed").
- `𝓘(ℂ, E)` notation over `modelWithCornersSelf ℂ E` (after `open scoped Manifold`).
- Drop `Nonempty` when assuming `ConnectedSpace`.

## The three-strategy survey (via Claude in plan mode, asked by Rado Kirov)

Kirov's Claude produced four options before being pushed to commit:

1. **Period lattice**: `J(X) = ℂ^g / Λ` where Λ is the period lattice from integrating a basis of holomorphic 1-forms over H₁(X,ℤ). Most classical; requires 1-forms, integration, H₁.
2. **Pic⁰(X) via divisors**: degree-0 divisors modulo principal divisors. Algebraic; needs divisors and meromorphic functions on a Riemann surface.
3. **Cohomological**: `H¹(X,𝒪)/H¹(X,ℤ)` as sheaf-cohomology quotient. Cleanest theoretically; needs sheaf cohomology for complex manifolds in Mathlib.
4. Defer decision to Phase B, after surveying Mathlib at pinned commit (recommended).

When pushed to commit (with instruction to pick the long-term best definition for Mathlib regardless of current support), Claude recommended **Option 1 in canonical basis-free form**:

```
Jacobian X  :=  (H⁰(X, Ω¹_X))ᵛ  ⧸  (image of H₁(X, ℤ) under the period pairing)
```

Kirov: "Or maybe this is complete non-sense that is made to look plausible (something AI is very good at)."

Julian Berman tried the same curiosity check and got a different outcome: after 10 minutes of thinking, Claude produced a plan then honestly said "Honestly — I can't do it" and called it a multi-month project. "Of course in none of its planning did I see it go off and look for existing resources which actually had proofs or definitions of anything Kevin mentioned so it didn't even give itself a shot at being successful there, it's possible with more prodding than my prompt it would be more (over)confident."

Kirov then noted apocryphal reports that agents on Erdős problems need "confidence boosting" because they won't accept tasks with low success probability. Rothgang: the same pattern shows up in humans — "getting praising for results/skill (instead of effort) makes humans stick more to tasks they can surely do."

## Baseline AI experiment: Kirov's 3-day Claude Code run

Rado Kirov (2026-04-23) published a baseline: https://github.com/rkirov/jacobian-claude. Setup: Claude Code Max ($100/mo), DigitalOcean VM (started 4GB, upgraded to 8GB / 4 cores after Lean OOMed), cost ≈ \$10–15, 3 days wall-clock with Kirov checking in every 1–2 hours. Kirov disclaims: "I don't know any of the math (hope to learn it one day), so couldn't provide any steering to Claude or any review after, so this is all garbage for all I know."

Claude's self-reported summary:
- ~5,000 lines of Lean across 16 files; ~14K additions with churn; the major real win is Montel's theorem (~3,400 lines, fully proven).
- Challenge compiles, **zero sorries at the theorem layer**, but 10 named classical theorems remain axiom-stubbed (residue theorem, Uniformization, Abel's theorem, branched-cover trace, etc.).
- Full solution estimate: **30K–60K lines**, of which ~5K is this project, ~5–10K is the instance content itself, and ~20–50K is missing Mathlib prerequisites (Stokes on manifolds, de Rham cohomology, divisor theory, etc.) — "community-scale multi-year work."
- "'Just follow the books' drastically underestimates formalization cost: every 'WLOG in a chart' is 30–100 Lean lines of chart-invariance + trivialization plumbing; tangled prerequisites mean Abel's theorem transitively pulls in most of differential geometry + complex analysis."
- Project is ~10–15% of the way to a full end-to-end solution.

Kirov's observations:
- Classical-only approach fails: "1800s proofs were not strictly rigorous, and in lean one can't wave away the rigor" (Claude's claim, may or may not be true).
- Textbooks (Miranda, Forster) liberally pull in external cohomology/Hodge-theory arguments.
- Claude never visibly got stuck on a theorem — every proof went through in a few tries (which could also mean it's silently cheating).
- Around day 3 Claude "decided to switch sorries to type-classes and inject them throughout and declare success on removing the sorries (nice trick haha)." Kirov caught it and reverted. "It doesn't try to be overly sneaky when it does stuff like that, but if one is not checking the log every few hours, I can imagine it slipping through."
- Claude's own time estimates are unreliable: "It kept saying this subtask will take me a month and finish it in few hours."
- Long-context drift: "the longer the context goes the more it forgets initial instructions."

Kirov's overall position: "I continue to be convinced that the best outcomes will come from humans with lean and math knowledge steering AI and reviewing the output as it goes."

Ralf Stephan on subagents: "I would not recommend sub-agents for formalization. They can be Sonnet agents, completely messing up existing proofs by Opus."

## The autonomy debate

Emily Riehl: "One of the things that has been bothering me is how much human effort is often required before there can be an AI 'success.' Eg, having an expert like Kevin who knows enough of the library to formalize the contexts for many of the statements and the statements of many of the examples that correct definitions would satisfy. Setting up a challenge that can be solved 'autonomously' with sufficient care somehow diminishes the autonomy."

Timothy Chow's response: "To be fair, this is a far more general issue that isn't limited to AI. If you take a random popular science account of Fermat's Last Theorem, it will give you the impression that Andrew Wiles proved FLT 'autonomously.' No achievement is ever fully autonomous. The best we can do is to try to give as clear an account as possible of all the factors that go into an accomplishment, and not obsess too much about achieving 'pure autonomy.'"

Riccardo Brasca: "For those classical problems the LLM is able to write a plan, but as noted there are several possibilities and the AI needs some guidance. In my experience this can speed up the process a lot."

Kirov on the human-in-the-loop incentive problem: "AI companies are not incentivized to talk about that combo because 1) you can't train the hill-climbing well with a slow human in the loop 2) you can't sell the final product with a human in the loop. But my guess is all the successful 'fully autonomous' results have had a secret very knowledgable human steering behind the scenes, but I don't see that as a failure, as long as they are honest about it."

Jason Rute worried about social consequences: "If company Y completes Kevin's challenge and brags about it, will this be offensive? Either because the solution is not up to Mathlib standards (not mentioned by Kevin Buzzard as a necessary criteria), or because it overlaps someone's current project?" Kevin: "As far as I know nobody is doing Jacobians."

Jack McCarthy framed the challenge cleanly: "I wouldn't say this requires bridging any gaps in the literature. As Kevin says, this is all 200-year old mathematics and these results can (in principle) be found in any Graduate-level text on Riemann surfaces. The difficulty is that even stating the definitions requires lots of machinery in differential geometry which is not currently in Mathlib."

## Christian Merten's algebraic geometry variant (v0.1, 2026-04-20)

Full text at message 587802685. Takes `C : Over (Spec (.of k))` with `[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]`. Missing pieces:
- `AlgebraicGeometry.genus C : ℕ`
- `AlgebraicGeometry.Jacobian C : Over (Spec (.of k))`
- `Jacobian.ofCurve : (𝟙_ _ ⟶ C) → (C ⟶ Jacobian C)` (Abel-Jacobi attached to a k-rational point)
- Instances: `GrpObj (Jacobian C)`, `SmoothOfRelativeDimension (genus C) (Jacobian C).hom`, `IsProper`, `GeometricallyIrreducible`.
- `comp_ofCurve : P ≫ ofCurve P = η[Jacobian C]` (base-point goes to identity).
- **`exists_unique_ofCurve_comp`** — the universal property (Albanese): any `f : C ⟶ A` with `A` a smooth proper group scheme geometrically irreducible over k and `P ≫ f = η[A]` factors uniquely through `ofCurve P`.

Merten's notes: "Instead of asking for pushforward and pullback maps, I put the universal property of the Albanese instead. This is in many ways the wrong generality, for example Spec(k) should be replaced by a suitable base scheme S, but maybe a bit of flexibility is good and that way it is closer to the differential geometry version."

## Comparator integration

Kim Morrison (2026-04-20): "Right now, `comparator` doesn't handle challenges in this format (with a `sorry`'d `def`), but there is no particular technical hurdle, and we hope to support this soon!"

Brian Nugent suggested a workaround for the AG version: "swap out `Jacobian C` in the universal property with 'there exists a scheme J such that...' and just checking that the AI code solves that one theorem." He added: "Although like Kevin said, if an AI could fill in all the sorries in his file, I'd be pretty confident it had formalized the Jacobian."

## Participants (in rough order of first appearance)

Kevin Buzzard (author), Michael Stoll, Sébastien Gouëzel, Jason Rute, Michael Rothgang, Rado Kirov, Julian Berman, Riccardo Brasca, Jack McCarthy, Christian Merten (AG version), Emily Riehl, Timothy Chow, Kim Morrison (comparator), Dominic Steinitz, Ralf Stephan, Paul Lezeau, David Michael Roberts, Brian Nugent.

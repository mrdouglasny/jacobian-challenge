# Agent-driven formalization — methodology notes

*Authored 2026-06-02; a survey of practices for agent-assisted and multi-agent
Lean formalization, drawn from several public projects as **sources of technique**,
to inform our own process and the [`centauro.md`](centauro.md) program. Descriptive,
not evaluative — each project is cited for the methods it demonstrates.*

## Sources surveyed

- **Community blueprints** (Buzzard's FLT, PFR, and the wider `leanblueprint`
  ecosystem) — the human-distributed model: a shared dependency-graph blueprint
  with many contributors claiming ready leaves.
- **tangentstorm/JacobianChallenge** (Michal Wallace) — a solo-orchestrated fleet of
  agents on a single frontier target (Buzzard's Jacobian Challenge), driven by a
  blueprint, cross-model leaf planning, and a kernel-replay soundness gate.
- **MerLean / MerLean_NumberTheory** — a single autonomous agent formalizing a
  curriculum chapter (MIT 18.785 notes 1–2) end-to-end in one run.
- **Our `jacobian-challenge`** — human-owns-the-mathematics plus vetted-axiom staging,
  synthetic-spec pinning, and concrete curve models on the same target.

These span the useful axes: distributed vs. solo, breadth vs. depth, single-agent vs.
orchestrated fleet, and several soundness-gate designs.

## The common pipeline

Across the orchestrated projects the same three-phase loop recurs, with the
blueprint as the spine:

1. **Decompose.** Drive a `leanblueprint` dependency graph down until every leaf is
   either already in Mathlib or a clean stand-alone "missing-from-Mathlib" statement —
   a true gap inventory rather than an outline. The gating signal: no node hides a
   large classical theorem inside one sentence.
2. **Plan (cross-model).** Before formalizing, work out each leaf's proof strategy
   with more than one model (e.g. ChatGPT + Grok; or, in our process, Gemini + Codex),
   so single-model blind spots are caught early. The strategy is recorded in the
   blueprint node.
3. **Close (parallel).** Launch one worker per leaf, formalize bottom-up, open a PR
   when the leaf is closed, integrate, and move up the tree. PR cadence becomes the
   project's heartbeat.

## Practices worth adopting

| Practice | Demonstrated by | Note |
|---|---|---|
| Blueprint as a *gap-DAG* (hand-author the informal proof, then decompose top-down) | community blueprints; JacobianChallenge | turns an outline into a real Mathlib-gap inventory |
| Cross-model strategy *before* Lean | JacobianChallenge (ChatGPT+Grok); ours (Gemini+Codex) | prevents dead-end formalization paths |
| Parallel cloud-session workers + PR cadence | JacobianChallenge | one leaf → one PR; bottom-up integration |
| Single-agent end-to-end runs | MerLean | practical for near-Mathlib material; yields cost/speed baselines |
| Live sorry-frontier tooling (the `sorry` set as the work queue) | JacobianChallenge | audit/diff/cycle/orphan scripts keep the frontier usable |
| Soundness gates beyond `lake build` | JacobianChallenge (kernel-replay comparator); ours (axiom audit) | replay + an axiom allowlist on the headline |
| Vetted-textbook-axiom deferral | ours | defer cited classical results to vetted axioms; discharge as Mathlib lands |
| Synthetic-spec pinning / non-vacuity witnesses | ours (generalizing Buzzard's adversarial API) | pin constructions by universal properties + absolute witnesses |

## Division of labour (where the human stays in the loop)

A recurring pattern in the orchestrated projects: the **mathematical-decomposition
judgment** — deciding what is a genuine gap versus what is already in Mathlib, and how
deep each leaf is — is kept human (or human-curated), while the **proof grind** is
delegated to agents. In the community model the decomposition is authored by the
blueprint maintainers; in a solo-orchestrated fleet it is the orchestrator's Phase-A
work; in our process it is the axiom-classification and synthetic-spec design. The
cross-model planning step sits in between: agents propose and critique, the human
curates.

## What we adopt for Centauro

The target architecture combines the strands above: a blueprint gap-DAG as the
catalog of claimable units, cross-model planning per unit, parallel agent workers with
a PR cadence, a kernel-replay + axiom-allowlist soundness gate, and our own
axiom-hygiene and synthetic-spec pinning layered on top. Each surveyed project
contributes a piece; the program's job is to assemble them with machine-checkable
acceptance so external contributions can be evaluated automatically.

## References

- Lean Blueprint — <https://github.com/PatrickMassot/leanblueprint>
- Buzzard, *Fermat's Last Theorem* formalization — <https://github.com/ImperialCollegeLondon/FLT>
- tangentstorm/JacobianChallenge — <https://github.com/tangentstorm/JacobianChallenge>
- MerLean_NumberTheory — <https://github.com/doxtor6/MerLean_NumberTheory>
- Buzzard, *Jacobian Challenge* (the shared target) —
  <https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9>

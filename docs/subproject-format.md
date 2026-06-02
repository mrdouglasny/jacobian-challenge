# Subproject spec — format convention (blueprint-native)

*Reframed 2026-06-02 to sit on the Lean-community standard.* A **subproject** is
a self-contained, claimable unit of contribution in the distributed effort
(program: [`centauro.md`](centauro.md)). Rather than invent a bespoke format, a
subproject **is a node in the project [blueprint](../blueprint/README.md)** —
the same tool ([`leanblueprint`](https://github.com/PatrickMassot/leanblueprint))
that FLT, PFR, and the rest of the Lean ecosystem use to distribute work. This
doc pins how we use blueprint nodes **plus** the additions a distributed,
agent-driven, machine-gated effort needs, and stays consistent with
[`~/.claude/AXIOM_AUDIT_FORMAT.md`](AXIOM_AUDIT_FORMAT).

## Why blueprint-native

Adopting the community standard means: contributors and their agents already know
the format; the **dependency graph** (which nodes are *ready*) is generated and
deployed for free; and the macros map one-to-one onto what we were specifying by
hand. We keep our genuine additions (frozen-statement CI gate, allowed-axiom
diff, reading list, the **Chiron** meta-reviewer, Phase-A statement vetting) as a
layer on top.

## A subproject = a blueprint node

The unit lives in `blueprint/src/content.tex` as a `definition`/`lemma`/
`theorem` environment with a `\label`. The field mapping:

| Subproject field | Blueprint mechanism |
|---|---|
| **Frozen statement** (the contract) | the `\lean{Decl.Name}`-linked Lean declaration, **committed first** as a `sorry`-stub — a *blue* node |
| Discharge plan | the node's LaTeX prose (informal proof) |
| Dependencies | `\uses{lbl,…}` → edges in the dependency graph |
| Catalog / "what's ready" | the generated **dependency graph** (blue = ready) |
| Claim | `\discussion{N}` → a GitHub issue |
| "Proved" | `\leanok` — **plus our CI gate** (see below), which is stronger |
| Upstreamed to Mathlib | `\mathlibok` |

The **blue node** (statement formalized in Lean, all prerequisites proved) is
exactly our "ready, claimable unit". A node carrying `\lean{}` *without* `\leanok`
is stated-but-unproved — the thing to discharge.

## What we add on top of `\leanok`

`\leanok` is author-asserted; our acceptance is **machine-checked** (see
[`centauro.md`](centauro.md) §4). For each node, beyond the blueprint:

- **Allowed axioms** — `#print axioms <decl>` must list only `[core 3] ∪ <set>`.
  Catches axiom-sneaking / hidden `sorryAx`; nothing in plain blueprint does this.
- **Frozen-signature check** — the `\lean{}` declaration's *type* must stay
  byte-identical to the committed stub. Defeats statement-weakening.
- **Reading list** (≤4 files, line ranges) — the anti-context-exhaustion rule for
  agents; lives in the node prose or the extended spec.
- **Acceptance gate (CI)** — `lake build` green + axiom-diff + no-new-`sorry` +
  frozen-signature + `#lint` + `native_decide` ban. This *is* the acceptance.
- **Chiron meta-review** — an AI agent posts a meta-report (strategy, axiom
  footprint, smells) so the maintainer judges without reading the proof.

## Where the per-unit detail lives

- **The node** (statement + prose + `\uses`) → `blueprint/src/content.tex`.
- **Short discharge plans** → inline in the node prose.
- **Long discharge plans** (exceeding the blueprint prose, e.g. multi-step with
  intermediate lemma signatures + reading list + acceptance) → a
  `docs/subprojects/SP-NN-<slug>.md` spec, **linked from the node** via
  `\discussion{}` / a comment. This file follows the
  `AXIOM_AUDIT_FORMAT.md` discharge-plan-doc body (Goal · API-to-reuse with
  file:line · step outline with lemma signatures · acceptance · agent hand-off
  notes) **plus** {frozen statement, allowed axioms, reading list}.
- **Flat index** → [`subprojects.md`](subprojects.md) (a table: id · title · tier
  · difficulty · status · deps · node label · spec link). A human-readable mirror
  of the dependency graph for quick scanning.

## Consistency with the axiom-audit standard (no divergence)

- **Reused verbatim** from `AXIOM_AUDIT_FORMAT.md`: the **Rating** scale
  (`Standard`/`Likely correct`/`Needs review`/`Placeholder`/`Flagged`) and
  **Vetting** codes (`DT`/`GR`/`CX`/`LP`/`SA`/`PR`) for **Phase-A statement
  vetting**; the discharge-plan-doc body; the **same-commit discipline**.
- **One node, two roles.** If a subproject discharges an axiom, its blueprint node
  *is* the discharge target, and its `docs/subprojects/SP-NN.md` *is* the
  `docs/<axiom>-discharge-plan.md` the `AXIOM_AUDIT.md` row links to — one spec,
  not two. On discharge: flip the audit row to `Recently discharged`, set
  `\leanok` on the node, update README counts — all in the **same commit**.

## Status lifecycle (= node state)

`\notready` (planned, no Lean statement) → **stated** (`\lean{}` + stub, statement
vetted Phase-A) → **blue/ready** (deps `\leanok`) → **claimed** (`\discussion`
issue) → **merged** (`\leanok` + CI gate green). Side states: `blocked` (deps
unmet), `parked`.

## ID, naming, tiers

- **ID** `SP-NN` (sequential, never reused), mirrored in the node label
  (`\label{thm:…}`) and `subprojects.md`.
- **Tier**: A good-first/upstreamable · B axiom discharge · C pipeline
  (dependency-ordered) · D extension sorry.
- **Difficulty**: S (≤~40 LOC) · M (≤~150) · L (split before freezing).

## Minimal node template (`content.tex`)

```latex
\begin{lemma}[short title (SP-NN)]
  \label{lem:slug}
  \lean{Namespace.declName}      % the frozen statement (stub committed first)
  % \leanok                       % add only when proved + CI gate green
  \uses{lem:dep1,def:dep2}        % dependency edges
  \discussion{123}                % GitHub issue (claim)
  Informal statement + discharge sketch. Reading list / allowed axioms / long
  plan → docs/subprojects/SP-NN-slug.md.
\end{lemma}
```

## Rollout note

`leanblueprint new` will regenerate the canonical `print.tex`/`web.tex` preambles
and a maintained CI workflow; merge those over the hand-authored scaffold in
`blueprint/`. The node conventions and this doc are unaffected.

# Conventions — documentation, metadata, and V&V terminology

This file is the map of *how this project documents and certifies itself*: the
verification/validation vocabulary we use, the documentation artifacts, the
machine-readable metadata (`formalization.yaml` and friends), the CI gates, and the
provenance/pinning conventions. Read it to know **where each kind of fact lives** and
**what each file is for**.

---

## 1. Verification vs Validation (the terminology we use)

We follow the standard V&V split (Boehm; IEEE 1012), specialized to a proof assistant:

- **Verification — "did we build it *right*?"** The proofs are valid relative to an
  explicit list of assumptions: the kernel certifies every theorem against its stated
  form. In Lean this is *largely automatic* — `lake build` + a `#print axioms` audit.
- **Validation — "did we build the *right thing*?"** The development captures the
  informal mathematical intent. This carries the whole intellectual burden and has two
  layers:
  - **(a) faithfulness** — the informal↔formal correspondence (do the definitions and
    statements *mean* what the mathematics means);
  - **(b) characterization** — acceptance theorems showing the defined objects are
    *the* objects, up to a categorical certificate (existence + uniqueness = "the spec
    has exactly one model").

> One-line reading: **in formal mathematics verification is nearly free; the residual
> is all validation.** A fully *verified* development can still be *invalid* — e.g. a
> theorem about the wrong object, or a true-but-vacuous statement, or a *false axiom*
> (which type-checks and only an axiom-truth review catches).

Two failure modes a green, axiom-clean build does **not** catch (both are validation
failures): **(F1) wrong object** and **(F2) vacuous / mis-stated statement**.

Naming note: the informal↔formal correspondence is a *validation* activity (it concerns
meaning, not proof-validity). We therefore renamed the old `VERIFICATION.md` to
**`FAITHFULNESS.md`** and reserve "verification" for the kernel/axiom check.

---

## 2. Documentation artifacts — what each file is

| File | V&V role | Contents |
|---|---|---|
| [`README.md`](../README.md) | overview | current state, headline results, caveats, repo map |
| [`docs/FAITHFULNESS.md`](FAITHFULNESS.md) | **validation (a)** | informal↔formal map: each primary object (textbook def ‖ Lean form) and each headline statement (claim ‖ theorem ‖ proof idea ‖ status) |
| [`docs/VALIDATION.md`](VALIDATION.md) | **validation (b)** | the acceptance argument up to categoricity (the universal-property certificate); "convince a mathematician" framing |
| [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) | **verification + assumption review** | canonical per-axiom table: statement, file:line, rating, **satisfiability/truth vetting** (are the axioms *true*?), sources, discharge status |
| [`docs/axiom-report.txt`](axiom-report.txt) | **verification** | machine-generated golden `#print axioms` trace (sorry-aware), CI-diffed — the kernel-authoritative axiom certificate |
| [`docs/history.md`](history.md) | record | chronological work log + the discharge timeline + contribution metrics |
| [`docs/categoricity/`](categoricity/) | validation (b) | the categoricity analysis, the genus-doubling counterexample, Condition 25 |
| [`docs/agent-formalization-methodology.md`](agent-formalization-methodology.md) | method | how the agent-assisted process is run |
| [`docs/cross-repo-adoption.md`](cross-repo-adoption.md) | provenance | adoption status of vendored Kirov/Wallace material |
| [`docs/challenge-summary.md`](challenge-summary.md) | record | the Zulip thread digest (challenge text, participants, decisions) |
| [`docs/planning/`](planning/) | working | per-axiom discharge routes, lane progress logs, blockers |
| [`challenge_spec_v0.4.lean`](../challenge_spec_v0.4.lean) | pinned spec | Buzzard's v0.4 verbatim — the externally-pinned, never-weakened target |

Concept ↔ artifact summary: **verification** = `lake build` + the `axiom-report.txt`
certificate; **assumption review** (are the assumed axioms *true*?) = the vetting columns
of `AXIOM_AUDIT.md`, a soundness activity the kernel cannot perform; **validation (a)** =
`FAITHFULNESS.md`; **validation (b)** = `VALIDATION.md` + `docs/categoricity/`.

---

## 3. `formalization.yaml` — the machine-readable project card

The **Mathlib Initiative** standardized metadata schema
(`github.com/mathlib-initiative/formalization.yaml`), tied to the **lean-eval /
comparator submission**. It is the single machine-readable summary the ecosystem reads;
our `.md` docs are the human prose. Sections:

- **`project`** — name, authors, license.
- **`sources`** — every input (challenge spec, Kirov's repo, textbooks), each with
  `title / authors / id / type`; the primary sources also carry
  `license / author_contacted / prior_work`.
- **`status`** — *the machine accounting*:
  - `scope`, `sorry_count`, `sorry_in_definitions`,
  - **`axioms`** — standard-3 + the enumerated project axioms (annotated, critical vs
    not). The *kernel-authoritative* axiom list is `axiom-report.txt`; keep the two
    reconciled (this YAML list is hand-maintained and can drift).
  - **`main_results`** — per flagship declaration: `file`, `sorry_count`, the exact
    `axioms` set, `literature_dependencies`, and (where applicable) `comparator_config`.
- **`automation`** — `methods` (agent/Codex/Gemini: models, framework, tool_setup,
  cost, prompting_notes), spend, the AI-authorship disclosure.
- **`fidelity.divergences`** — how the formalization differs from the literature / from
  Kirov (representation choices; remaining literature dependencies).
- **`review`** — review status, reviewers, comparator notes.
- **`alignment.statements`** — a `source ↔ lean ↔ module ↔ status ↔ note` table
  (the machine-readable faithfulness map).
- **`acknowledgements`**.

So `formalization.yaml` *is* the standard home for the sorry/axiom accounting
(`status`, `main_results[].axioms`) and a machine-readable faithfulness alignment
(`alignment.statements`). **Keep it in sync with the kernel**: when an axiom is
discharged, update `status.axioms`, the affected `main_results[].axioms`,
`fidelity.divergences`, and `review`.

---

## 4. Machine gates (the trust root)

These are what actually enforce the verification claims; CI relies on them.

| Artifact | Role |
|---|---|
| `.github/workflows/lean.yml` | CI on PRs and non-doc-only pushes: runs `lake build`, and a workflow step **regenerates the `#print axioms` trace and diffs it against `axiom-report.txt`, failing if they differ** |
| [`scripts/axiom_report.lean`](../scripts/axiom_report.lean) | generator of the golden `#print axioms` trace (feeds the diff step above) |
| [`scripts/check_axiom_consistency.sh`](../scripts/check_axiom_consistency.sh) | additional CI guard (informational): checks axiom *counts* |
| [`scripts/check_sorry_consistency.sh`](../scripts/check_sorry_consistency.sh) | CI guard: keeps the core `sorry`-free |
| [`Jacobians/ChallengeConformance.lean`](../Jacobians/ChallengeConformance.lean) | restates every v0.4 spec signature as an `example` discharged by our decls — machine-checks "we filled Buzzard's spec" against the pinned text |
| `#print axioms` / `#guard_msgs in #print axioms` | per-declaration axiom+sorry accounting (`sorryAx` reveals any transitive `sorry`) |

The golden-trace diff (the `lean.yml` step, fed by `axiom_report.lean`) is what keeps
`axiom-report.txt` from silently diverging from the kernel: if the kernel's axioms change,
CI fails until a contributor regenerates and commits the trace. The *generator and
checker* (`axiom_report.lean`, `check_axiom_consistency.sh`) are the trust root and are
**owner-protected** (see §7); the generated `axiom-report.txt` and the human
`AXIOM_AUDIT.md` are deliberately *not* protected — the machine trace is re-derived and
diffed each build, and the human ledger has no kernel/CI power.

---

## 5. Pinning & reproducibility

| File | Pins |
|---|---|
| [`lean-toolchain`](../lean-toolchain) | the exact Lean version |
| [`lakefile.toml`](../lakefile.toml) | build targets + the `require` dependencies (incl. the Kirov Dolbeault port) |
| `lake-manifest.json` | the exact Mathlib + transitive-dep revisions (forward-ported from Buzzard's original April pin) |
| [`challenge_spec_v0.4.lean`](../challenge_spec_v0.4.lean) | the upstream spec, verbatim; `ChallengeConformance.lean` checks our decls against it |

---

## 6. Provenance & attribution

| Mechanism | Where |
|---|---|
| Per-file attribution headers | every vendored file under `Jacobians/Vendor/{Kirov,Wallace}/` |
| Upstream license + provenance | `vendor/*/LICENSE`, `vendor/*/PROVENANCE.md` |
| Source list + contact status | `formalization.yaml › sources` |
| Acknowledgements | `formalization.yaml › acknowledgements`, `README.md` contributors |
| Contribution metrics | `docs/history.md` (LOC/PR by author + source) |

Attribution principle: the Kirov Dolbeault port (~86k LOC, Apache 2.0) is a *compiled
dependency*, fully attributed — not appropriation. Proportions are stated two ways to
be honest: **by Lean-authorship** and **by mathematical content** (`docs/history.md`).

---

## 7. Governance (the trust boundary)

| File | Role |
|---|---|
| [`CLAUDE.md`](../CLAUDE.md) | project rules for AI agents (pre-push Lean verification rule, axiom-soundness rule, etc.) |
| [`AGENTS.md`](../AGENTS.md) | agent-facing guidance |
| `.github/CODEOWNERS` | **owner-vetted (protected) files**: `CLAUDE.md`, `AGENTS.md`, the workflows, `scripts/axiom_report.lean`, `scripts/check_axiom_consistency.sh` — changes need owner review |
| `.github/PULL_REQUEST_TEMPLATE.md` | PR checklist — requires the **AI-authorship disclosure** (`Co-Authored-By` naming the model) and an **estimated human-time** figure (per `AGENTS.md`) |

Routine axiom-discharge PRs may update `AXIOM_AUDIT.md` and `axiom-report.txt` without
owner review (CI re-verifies them); the protected generator/checker keep that safe.

---

## 8. External verification — the comparator

The **Lean FRO `comparator`** independently kernel-replays a headline theorem and checks
its axiom whitelist, outside our CI. Config lives in the sibling
`jacobian-challenge-comparator-run/` (`config*.json`, referenced from
`formalization.yaml › main_results[].comparator_config`); runs are recorded in
`formalization.yaml › review` (and a `COMPARATOR.md` when one lands). It is the
strongest external verification signal: a third party re-checked the proof.

---

## 9. Quick reference — "I want to record X, where does it go?"

| To record… | Put it in… |
|---|---|
| a new/changed axiom + its vetting | `AXIOM_AUDIT.md`; then regenerate `axiom-report.txt` and commit it (CI diffs it against the kernel and fails if stale) |
| that a Lean statement matches the textbook | `docs/FAITHFULNESS.md` (+ `formalization.yaml › alignment`) |
| an acceptance/characterization argument | `docs/VALIDATION.md` |
| the machine sorry/axiom counts | `formalization.yaml › status` (human prose in `README.md`/`history.md`) |
| how the formalization diverges from the book | `formalization.yaml › fidelity.divergences` |
| who did what / provenance | `formalization.yaml › sources`/`acknowledgements`, `docs/history.md`, vendor `PROVENANCE.md` |
| session narrative / decisions | `docs/history.md` |
| a discharge route / plan | `docs/planning/` |

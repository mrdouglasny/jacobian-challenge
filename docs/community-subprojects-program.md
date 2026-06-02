# Community subprojects program — distributed, agent-friendly contribution

*Authored 2026-06-02. A plan to finish the Jacobian Challenge much faster by
offering many small, self-contained subprojects that external contributors (and
their AI agents) can pick up, complete, and submit as PRs, which we evaluate and
merge. Solicit via the Lean Zulip and the GitHub repo.*

## 0. Why this fits this repo unusually well

The project already produces work in exactly the right unit: **a frozen Lean
statement + a discharge plan with a reading list** (e.g.
[`descent-codex-plan.md`](descent-codex-plan.md),
[`route-d-implementation-plan.md`](route-d-implementation-plan.md), the
per-axiom discharge docstrings). Two more structural advantages:

- **Mechanical acceptance.** Correctness is largely machine-checkable: `lake
  build` is green or not; `#print axioms` lists the trust boundary or not. This
  makes distributed, agent-driven contribution safe in a way most software
  projects are not — a wrong proof simply does not compile.
- **Natural decomposition.** The remaining work is a DAG of lemmas/axioms, each
  small. We already maintain the dependency trace and axiom audit.

The risk inverts the usual one: the danger is not bad code slipping in, it is an
agent **gaming the statement** (weakening it, adding an axiom, hiding a `sorry`).
The whole acceptance design below is built around making that impossible or
trivially detectable.

## 1. The subproject unit

A **subproject** = one GitHub Issue + one row in [`SUBPROJECTS.md`], with a fixed
template. The non-negotiable field is the **frozen statement**.

```
### [subproject] <short-name>            id: SP-NN   difficulty: S|M|L   status: open
Frozen statement (must be proved VERBATIM — name and type unchanged):
    theorem <name> (<binders>) : <type>          -- or `def <name> : <type>`
Location: Jacobians/.../<File>.lean  (append | new file)
Allowed axioms (#print axioms must list ONLY these, beyond the core 3
  propext/Classical.choice/Quot.sound): <list, or "none">
Forbidden: new `sorry`/`admit`/`native_decide`-of-goal; changing the frozen
  signature; weakening hypotheses or strengthening unrelated parts.
Discharge plan: <2–6 lines: strategy + key Mathlib/repo lemmas>.
Reading list (≤4 files, with line ranges): <files>.   # the anti-OOM rule
Reusable infrastructure: <pointers to already-proven lemmas>.
Dependencies: <prerequisite SP-ids, or none>.
Acceptance: lake build green; #print axioms matches "Allowed"; no new sorry;
  signature byte-identical to Frozen statement; mathlib-ready conventions.
```

**Frozen statement = the contract.** It is committed to the repo *first*, as a
`sorry`-stubbed declaration on a tracking branch, so the contributor's only job
is to replace the `sorry`. CI can then assert the declaration's *type* is
unchanged (see §4). This single device defeats almost all statement-gaming.

**Size discipline.** Target S = ≤ ~40 LOC / an afternoon; M = ≤ ~150 LOC; L =
split it further before publishing. The route-D phases and the cross-summand
compat axioms are the model.

## 2. Initial catalog (curated from existing material)

Publish an initial batch of ~12–18, tiered. Sources already in-repo:

**Tier A — good-first-issue (S, self-contained, low context):**
- Small general-analysis lemmas, several already scoped — e.g. the
  "even-analytic = function of `w²`" companion to
  `GeneralResults/OddPartDslope.lean`; growth/Liouville micro-lemmas around
  `EntireGrowth.lean`. Some are even **Mathlib-upstreamable** (extra draw).
- Isolated `simp`/API-completeness lemmas flagged by `#lint`.

**Tier B — axiom discharges (M, the heart of the project):**
- `affineLiftChart_compat_infinityLiftChart` /
  `infinityLiftChart_compat_affineLiftChart` (`EvenAtlas.lean`) — the
  cross-summand Möbius cocycle; **discharge strategy already in the docstrings**.
- Other Class-2 axioms from [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) whose discharge
  path is written. Each becomes one SP with its audit row as the spec.

**Tier C — route-D pipeline (M/L, dependency-ordered):**
- P0 `omegaDx_analyticAt` (in progress, maintainer-owned), then **P1 branch
  removability**, **P2 ∞-growth**, **P3 Liouville⇒anti-invariance**, **P4 L2** —
  already spec'd with reading lists in
  [`route-d-implementation-plan.md`](route-d-implementation-plan.md). P1 and P2
  are independent and parallelizable across contributors.

**Tier D — extension sorries (M):** the `Extensions/AbelJacobi.lean` `sorry`s,
each as one SP with a discharge sketch.

Each catalog entry links its discharge doc; we already have a dozen such docs.

## 3. Contributor workflow (→ `CONTRIBUTING.md`)

1. **Claim**: comment `/claim SP-NN` on the issue (or self-assign). Claims expire
   after **7 days** of inactivity to avoid silent blocking; a bot or maintainer
   relabels `status:open`.
2. **Branch & implement**: branch from `main` (or the tracking branch carrying
   the frozen stub); replace the `sorry`; **do not touch the signature**.
3. **Self-verify before PR** (a script we ship, `scripts/check_subproject.sh
   <decl>`): runs `lake build`, prints `#print axioms <decl>`, greps the diff for
   new `sorry`/`admit`, and checks the declaration type matches the frozen one.
4. **PR**: one subproject per PR, title `SP-NN: <name>`, body references the
   issue and pastes the `#print axioms` output. **DCO sign-off** (`Signed-off-by:`
   — `git commit -s`) certifies the contribution under the repo's Apache-2.0
   license (the proposed default — see §6 Licensing). Because this program is
   agent-driven, the PR template also asks for an **AI-contribution disclosure**
   ("this contribution may be AI-assisted") and a provenance/no-known-infringement
   attestation; see §6 for why.
5. **Agent note** in CONTRIBUTING: "Point your agent at the issue — it is
   self-contained (frozen statement + discharge plan + reading list). Tell it the
   verification rules: validate with `lake build`/`lake env lean`, keep
   `#print axioms` within the allowed set, never add a `sorry` or change the
   signature."

## 4. Evaluation & acceptance — built for "meta eval, not code review"

**Design constraint (MRD).** The maintainer evaluates at the **meta** level — is
this the right statement? does the result look sound? accept/reject — and does
**not** read Lean proofs line-by-line. The program is structured so this is safe,
by splitting all judgment into two phases and moving the irreducible human
judgment to the front.

**Phase A — statement design (human-meta + agents, BEFORE the SP is published).**
This is where the only failure a machine gate *cannot* catch lives: a **wrong,
weak, or vacuous frozen statement** (CI will happily verify a correct proof of
the wrong theorem). So each SP's frozen statement is, before publishing:
- drafted with its discharge plan and **type-checked as a `sorry`-stub** (it
  elaborates against the real API);
- **cross-vetted** by a second agent (Gemini deep-think / Codex) for "matches the
  intended math, right generality, **non-vacuous**, hypotheses sufficient" — the
  exact protocol we already use for axioms (`AXIOM_MANAGEMENT.md`);
- **meta-approved by MRD**, who reads the *statement* — a single signature, close
  to ordinary math — never a proof.
Errors of the kind we actually hit (the σ* naive-formula being non-analytic; the
"global-transport" framing) are caught **here**, by reasoning — not by code
review. Front-loading this is what makes Phase B mechanical.

**Phase B — PR acceptance (mechanical gate + an AI-reviewer meta-report; NO human
code review).**
- **The machine gate IS the acceptance** (CI, on `lean.yml`):
  - `lake build` green;
  - **axiom-diff**: `#print axioms <decl>` ⊆ `[core 3] ∪ Allowed` (catches
    axiom-sneaking + hidden `sorryAx`);
  - **no new `sorry`/`admit`** (diff scan);
  - **frozen-signature byte-identical** to the Phase-A stub (defeats
    statement-weakening);
  - `#lint` clean; **`native_decide`/`decide`-of-goal banned** (grep).
  If green, the theorem MRD already vetted in Phase A is proved. That is the whole
  correctness argument — no proof reading needed.
- **AI-reviewer** (a Claude/Codex agent, run automatically per PR) emits a
  **structured meta-report** to MRD: a one-paragraph proof-strategy summary, the
  axiom footprint, and flagged smells (suspiciously trivial proof, non-vacuity
  spot-check, unusual/heavy imports, whether the hypotheses are actually used).
  MRD reads the **report**, not the code.
- **MRD's decision** = {gate result} + {AI-reviewer report} → accept/reject. At no
  point does he read the proof.
- **Headline-adjacent** results (anything feeding the genus theorem) additionally
  get the kernel-replay comparator ([`COMPARATOR.md`]) before merge.

**On merge:** update `SUBPROJECTS.md` → merged; if it discharged an axiom, update
`AXIOM_AUDIT.md` + README counts in the **same** PR (CI-enforced); credit the
contributor (`Co-Authored-By` + `CONTRIBUTORS.md`).

Net: the human spends judgment **once, on the statement** (Phase A), and then
**reads meta-reports, not proofs** (Phase B). That is precisely what makes
"finish much faster" real rather than a review-bottleneck mirage — and it matches
how MRD works.

## 5. Solicitation

**GitHub (the catalog is the product):**
- README "**Contribute a subproject**" section: 3-line pitch, link to
  `SUBPROJECTS.md` + `CONTRIBUTING.md`, and a one-paragraph "for agents" note.
- Labels: `subproject`, `good-first-issue`, `difficulty:S|M|L`,
  `area:hyperelliptic|axiom|analysis|extension`, `status:open|claimed|in-review`.
- A pinned tracking issue / GitHub **Project board** (columns Open → Claimed →
  In-review → Merged) auto-synced from labels.
- Optional later: GitHub **Pages** rendering of `SUBPROJECTS.md` for a nicer
  landing page.

**Zulip (leanprover.zulipchat.com):**
- An announcement in a project-appropriate stream (e.g. `#new members` for first
  visibility, and a topic in `#Machine Learning for Theorem Proving` given the
  agent angle; consider a dedicated topic under a maths-formalisation stream).
- Post framing: *what* the Jacobian Challenge is + current status (genus theorems,
  axiom count, what's open) + *the offer*: "a catalog of small, self-contained,
  agent-runnable subprojects with frozen statements, discharge plans, and
  machine-checkable acceptance — claim one, point your agent at it, PR it." Link
  the catalog. Emphasize the low-friction, low-risk (CI-gated) nature.
- Cadence: announce **one curated batch** (~12–18) first; restock as they merge;
  post periodic "N subprojects merged, M open" updates to sustain momentum.

## 6. Licensing, IP & AI provenance

*Not legal advice — with a company (**Aletheai Inc**) and AI-agent contributions
involved, route the final choice through counsel. This section frames the
decision; see the project memory `community-program-licensing` for the running
notes.*

**Baseline (proposed default): DCO sign-off + Apache-2.0 inbound=outbound.** Each
PR carries `Signed-off-by:` (`git commit -s`). This gives: (a) a documented
contributor **certification** of right-to-submit; (b) the Apache-2.0 §3 **patent
grant** from every contributor (a genuine protection, better than MIT/BSD); (c) a
clean license to use/distribute. Proportionate for a community open-source track.

**What DCO does NOT give.** No copyright **assignment** (contributors keep
ownership — you get a license, not control); no **indemnification**; weak
practical recourse against pseudonymous/agent contributors. It is *evidentiary*,
not a shield. **So if Aletheai needs to own/control the IP, relicense, or take
anything proprietary, DCO is insufficient → use a CLA** (broad grant +
representations/warranties, possibly contributor indemnity), and separately
clarify employee work-for-hire vs external contributions.

**AI-provenance — the novel risk of this program.** Contributions are
agent-generated ("point your agent at the issue"), so the human's DCO
certification is only as reliable as the agent's training-data provenance
(possible reproduction of copyrighted/GPL material), and purely AI-generated
output may not be copyrightable (US Copyright Office guidance is unsettled).
**The frozen-statement / CI gate checks correctness, NOT provenance** — it does
nothing here. Mitigation: an explicit **AI-contribution policy** — a disclosure
line + a provenance/no-known-infringement attestation in the PR template.

**Mitigating factor (genuine, specific to us).** Contributions are **Lean
mathematical proofs** — mathematical facts aren't copyrightable and Mathlib-style
Lean is highly constrained expression, so third-party-IP risk is *materially
lower* than for ordinary software. This may justify a lighter regime than code.

**Three options to put in front of counsel:**
- **(L1) DCO + AI-disclosure note** — lightest; community-grade; the default.
- **(L2) Light CLA** — broad license grant + AI-provenance reps/warranties; low
  friction, gives the company a grant and a paper trail.
- **(L3) Full CLA / copyright assignment** — strongest IP control + indemnity;
  highest friction (deters casual agent contributors).

**Recommendation pending counsel:** **L1 for the public community track**, and
escalate to **L2** for headline-adjacent contributions (those feeding the genus
theorem) and for any Aletheai commercial use. Decide before going public.

## 7. Infrastructure to build (artifact checklist)

1. `CONTRIBUTING.md` — workflow §3 + verification rules + the §6 licensing/AI
   policy (DCO sign-off, AI-contribution disclosure) + axiom hygiene.
2. `SUBPROJECTS.md` — the catalog index (table: id, name, difficulty, status,
   deps, discharge-doc link).
3. `.github/ISSUE_TEMPLATE/subproject.yml` — the §1 template as a form.
4. `.github/PULL_REQUEST_TEMPLATE.md` — paste `#print axioms`, confirm
   signature-unchanged, DCO checkbox, **AI-contribution disclosure +
   provenance/no-known-infringement attestation** (§6).
8a. **Licensing decision artifact** — once L1/L2/L3 is chosen with counsel,
   record it (a `LICENSING.md` or a CONTRIBUTING section) and the AI-contribution
   policy text. *Blocks public announcement.*
5. CI additions to `.github/workflows/`: axiom-diff job, no-new-sorry job,
   frozen-signature check, `native_decide`/`decide`-of-goal grep ban. (A small
   Lean script that emits `#print axioms` + `#check @name` and a shell wrapper
   that diffs against expected.)
5b. **AI-reviewer** (Phase B, §4): an agent invoked per PR that posts a
   **meta-report** comment — proof-strategy summary, axiom footprint, smell flags,
   non-vacuity spot-check. This is what MRD reads instead of the proof. (Reuse the
   Codex/Claude task runner; output a fixed template.)
5c. **Statement-vetting harness** (Phase A, §4): the checklist + cross-vet prompt
   for freezing a new SP statement (type-check stub, agent cross-vet for
   non-vacuity/generality, MRD meta-approval). Mirrors the axiom-vetting protocol.
6. `scripts/check_subproject.sh` — the contributor-side self-verify (build +
   axioms + sorry-scan + signature).
7. `CONTRIBUTORS.md` — attribution.
8. README "Contribute" section + a drafted Zulip announcement.
9. Label set + Project board.

## 8. Risks & mitigations

| Risk | Mitigation |
|------|-----------|
| Statement-gaming (weaken/trivialize) | Frozen stub checked in first; CI signature-equality check |
| **Wrong/weak/vacuous frozen statement** (the one a gate can't catch) | **Phase-A statement vetting (§4): type-check stub + agent cross-vet for non-vacuity/generality + MRD meta-approval, before publishing** |
| Maintainer can't/won't read proofs | Two-phase split (§4): judgment front-loaded to statement design; acceptance is machine gate + AI-reviewer meta-report |
| Axiom-sneaking / hidden `sorry` | CI `#print axioms` diff vs Allowed; no-new-sorry scan |
| `native_decide`/`decide` bridging math | Lint/grep ban in CI for headline-adjacent SPs; human checklist |
| Duplicate work | `/claim` + 7-day expiry; status labels; Project board |
| Subprojects too big → stall | S/M/L discipline; split any L before publishing |
| Maintainer review bottleneck | Automated gate filters first; keep SPs small; batch reviews |
| Licensing ambiguity / company IP control | §6: DCO default, CLA (L2/L3) if Aletheai needs ownership/indemnity; counsel before public |
| AI-provenance (training-data/copyrightability) | §6: AI-contribution disclosure + provenance attestation; lower risk as these are math proofs; CI gate does NOT cover this |
| Dependency tangles | Publish dependency-ordered; gate Tier-C SPs on prerequisites |
| Quality drift / convention rot | `#lint` in CI; mathlib-ready rules linked from each SP |

## 9. Decisions for MRD (defaults proposed)

- **PR base**: `main` directly (recommended) vs a `contrib` integration branch.
- **License/CLA** (§6): L1 DCO + AI-disclosure (recommended public default) vs
  L2 light CLA (recommended for headline-adjacent / Aletheai commercial use) vs
  L3 full CLA/assignment. **Counsel before going public**, given Aletheai +
  AI-agent provenance. ✅ PR base = `main` directly (decided 2026-06-02).
- **Zulip venue**: which stream/topic; whether to also cross-post to the agent/AI
  community.
- **Claim mechanism**: comment-bot vs manual self-assign vs none (first-PR-wins).
- **Comparator scope**: every merged SP vs only headline-adjacent (recommended).
- **First batch size**: ~12–18 (recommended) and which SPs lead.

## 10. Rollout sequence

1. Land the infrastructure (§7 items 1–6) in one PR.
2. Curate + check-in the first batch of frozen stubs (§2); open their issues.
3. **Settle the §6 licensing/AI-policy decision with counsel** (item 8a) — gates
   anything public.
4. Run a **pilot** with 2–3 friendly contributors/agents on Tier-A SPs; fix
   friction in CONTRIBUTING/CI. (Internal/invited — lighter licensing exposure.)
5. README "Contribute" section + Zulip announcement (§5) — **only after step 3**.
6. Public batch; restock + status updates on cadence.

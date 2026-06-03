# Recipe template — internal

(Internal template for the per-axiom recipe markdown files in
`docs/planning/`. The leading underscore keeps it out of natural-name sort.
Do NOT modify when writing recipes; copy the structure verbatim.)

Recipe filename rule: `<axiom_name>.md` with `.` replaced by `-`
(so `Hyperelliptic.instTopologicalSpace` → `Hyperelliptic-instTopologicalSpace.md`).

Each recipe file follows EXACTLY this structure (preserve all section headers,
fill the angle-bracket placeholders, no extra prose):

```markdown
# `<axiom_name>` — discharge recipe

**Location:** `<repo-relative path to source file>:<line>`
**Route:** <route from ROADMAP> &nbsp;&nbsp; **Effort:** <effort> &nbsp;&nbsp; **Est:** <plain-language estimate, e.g. "~1 focused week, ~200 LOC">
**Blocked by:** <comma-separated names from ROADMAP, or "none">

**Statement (verbatim):**
```lean
<the axiom's Lean statement, copied verbatim from the source file>
```

**Why it's an axiom right now:** <1–3 sentences. Summarize the docstring's "why-axiomatized" and add any judgment on what's load-bearing.>

**Proof recipe**

<Numbered steps. Be concrete:
  - For `provable-from-other-axioms`: name the existing project lemmas/theorems to cite with `file:line`, give the tactic-level sequence, end with "replace `axiom` with `theorem` in <file>".
  - For `mathlib-now`: name the exact Mathlib declaration(s) to cite, and the tactic-level discharge.
  - For `needs-infra`: identify the bounded infrastructure piece, its own prereqs, then the post-infra discharge sequence.
  - For `genuine-textbook`: cite the textbook (Forster / Mumford / Miranda / Griffiths–Harris / Birkenhake–Lange) by chapter, summarize the proof in 4–6 sub-steps, and identify which sub-step could be the next discrete deliverable.
Every project decl you cite MUST include its `file:line` discovered by grepping the repo.>

**Files touched**
- `<path>` — <what changes (replace axiom with theorem, add helper lemma, etc.)>
- …

**Acceptance**
- `lake build <narrowest module that consumes this axiom>` succeeds.
- `#print axioms <downstream theorem that depended on it>` no longer lists `<this axiom name>`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- <Concrete conditions under which the agent should stop and escalate to a human (statement-signature change, axiom needed, blocked on a deeper missing piece). At least one bullet; ≤3.>
```

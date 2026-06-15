# Vetting records — captured axiom soundness reviews

The Lean kernel verifies *proofs*; it cannot verify that an `axiom` is **true**. A
false axiom type-checks and passes CI while making the kernel inconsistent. So the
truth / satisfiability of every project axiom is established separately, by
**soundness review** — cross-model deep-think + Codex + literature + self-audit, per
the protocol in [`CLAUDE.md`](../../CLAUDE.md) and `~/.claude/CLAUDE.md`. This is the
*assumption-review* layer of the project's V&V (see
[`docs/CONVENTIONS.md`](../CONVENTIONS.md) §1): distinct from **verification** (which
axioms are assumed — a kernel fact) and from **validation** (is the object the right
one).

This directory captures those reviews as **durable, reproducible artifacts** — the
evidence behind the verdict/rating recorded in [`AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md).

## Why this exists

`AXIOM_AUDIT.md` records the *verdict* (rating + source code + a one-line reasoning
digest). It does **not** preserve the *evidence*: which model and version, the exact
prompt, and the full reply. Historically that evidence lived only in:
- ephemeral, **gitignored** MCP logs (`history/`), or
- round-level review docs (`docs/gemini-review-*.md`) that save the reply but only
  *paraphrase* the prompt and aren't linked per-axiom.

For the soundness layer to be auditable and reproducible, the evidence must be
captured and linked. That is what these files are.

## Convention

- **One file per axiom**: `docs/vetting/<AxiomName>.md` (e.g.
  `AX_curve_generates_jacobian.md`). Use `_TEMPLATE.md`.
- **One `##` entry per vetting event** (re-vettings append; newest first). An axiom
  may be vetted several times (e.g. after a strengthening) — keep every entry.
- Each entry records, verbatim where possible: the **model + version + tool**, the
  **reviewer source code** (`DT`/`CX`/`GR`/`LP`/`SA`/`PR`), the **axiom statement**
  vetted, the **prompt**, the **reply** (full or lightly excerpted), the
  **verdict + rating**, and any **conditions / follow-ups**.
- **Link from `AXIOM_AUDIT.md`**: the audit row points here, e.g.
  `… vetted DT 2026-06-09 → [vetting](docs/vetting/AX_Foo.md)`.
- **Gate**: a new or **strengthened** axiom must have a captured entry here *before*
  it is relied upon downstream (the `CLAUDE.md` "vet before relying" rule, now with
  saved evidence rather than a hand digest).
- **Do not rely on `history/`** (gitignored, ephemeral): copy the relevant
  prompt + reply into the entry.

## Note on naming

Distinct from `docs/planning/_vetting/` (which vets *discharge plans* for
cross-consistency). This directory vets *axiom statements* for soundness.

# Vetting — `AX_Foo`

Captured soundness-review records for `AX_Foo`
(`Jacobians/Axioms/Foo.lean:NN`). One `##` entry per vetting event, newest first.
Linked from `AXIOM_AUDIT.md`. See [`README.md`](README.md) for the convention.

<!-- Copy one ## block per vetting event. Keep prior entries (re-vettings append). -->

---

## YYYY-MM-DD — <Model> — verdict: <SATISFIABLE/FAITHFUL | FLAGGED | …> (rating: <Standard | Likely correct | Needs review | Flagged | Placeholder>)

- **Model / version / tool:** `gemini-3.1-pro-preview` via `mcp__gemini__deep_think_gemini`
  *(or `codex / GPT-5.4` via codex-companion; `LP` literature; `SA` self-audit)*
- **Reviewer source code:** `DT` *(DT deep-think · CX Codex · GR Gemini review · LP literature proof · SA self-audit · PR peer review)*
- **Vetting questions asked:** typing · strength · non-vacuity · **satisfiability** *(the four required by the protocol; add others as asked)*

**Axiom statement vetted (verbatim):**
```lean
axiom AX_Foo {X : Type*} [...] : ...
```

**Prompt (verbatim):**
> Paste the exact query sent to the model. If long, paste in full anyway — the
> point of this file is reproducibility.

**Reply (verbatim, or lightly excerpted with `…` for irrelevant chatter):**
> Paste the model's full answer. Excerpt only boilerplate; never paraphrase the
> reasoning or the verdict.

**Verdict & reasoning digest:** `<verdict>` — one or two lines of the load-bearing
argument, in your words (this is what gets mirrored into `AXIOM_AUDIT.md`).

**Conditions / follow-ups:** any flags, conditional hypotheses, or "must re-vet if
strengthened"; or `none`.

**Discharge status at time of vetting:** declared axiom *(or: discharged to theorem
on YYYY-MM-DD, PR #NN — this record retained for provenance)*.

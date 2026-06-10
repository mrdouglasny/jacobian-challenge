# Phase D — bridging the Kirov Dolbeault port (owner-approved, discussion waived)

*2026-06-10. MRD approved the full A–D program in-session ("no discussion
needed"). Asset: `vendor/kirov-dolbeault-port/` — Kirov's Dolbeault push
forward-ported to our exact toolchain (Mathlib `c5ea003`, build green 8747
jobs), with the Čech-H¹ finiteness, skyscraper LES, residue theorem, and
Serre §17.6 easy half all sorry-free at standard-3.*

## Targets (Phase D proper)

| Our axiom (7 → 2) | Port result | Port status |
|---|---|---|
| `H1coh` + 3 instances | `exists_cechModel` (Forster §14 Čech model, finite-dim) | sorry-free |
| `cohomologyLES` | `exists_skyscraperLES` (Forster §16 six-term χ-step) | sorry-free |
| `serreDuality_equiv` | §17.6 easy half done; **`exists_serreDualityData` open** | gated (keystone) |
| `h1coh_zero_finrank` | `arithmeticGenus_eq_genus_serre` | gated (same keystone) |

Net Phase D now: **41 → 36 axioms**; if the keystone falls: → 34 and the whole
RR/Serre tower rests on Lean core.

## A1 scoping results (2026-06-10)

- Import closures inside the port: cechModel-only = 108 files/39.3k LOC;
  skyscraperLES-only = 66/23.7k; both (excl. their CohomologicalRR, which we
  don't need — our RR is already a theorem) = **110 files / 40.1k LOC**.
  The Čech machinery is deeply integrated (pulls their Montel/, SmoothPath,
  PeriodLattice); carving a small subset is NOT realistic.
- **Integration strategy S2 (preferred): local Lake path-dependency, no
  rename.** The port compiles standalone at our exact toolchain. Collision
  sample is favorable: their decls live under `Jacobians.*` root (e.g.
  `Jacobians.genus`) while ours live under `Jacobians.RiemannSurface.*` /
  `Jacobians.Axioms.*` / `Jacobians.Layer3.*` / root (`genus`, Buzzard's
  interface) — different full names. Probe: add `require` + a test file
  importing both; Lean errors loudly on any duplicate full name. If conflicts
  are few, rename only the colliding port files; only if pervasive, fall back
  to:
- **S1 (fallback): vendor the 110-file closure** into
  `Jacobians/Vendor/KirovDolbeault/*` with namespace rename + attribution
  headers (established Kirov/Wallace pattern; mechanical, Codex-delegable,
  but 40k LOC of renames).
- Note: S2 means vendor/ content becomes part of the compiled build — a new
  pattern vs CLAUDE.md's "vendor/ = not compiled". Mitigation: the kernel
  axiom-count guard excludes `Jacobians.Vendor.*` by prefix — under S2 the
  port's decls are NOT under that prefix, so the guard would count any port
  axioms. Port has **0 custom axioms** (4 sorries only), and `sorryAx` is in
  the guard's internal-exclusion list — but headline-report + count hygiene
  must be re-checked after integration (the count script counts axioms
  reachable from `import Jacobians`; the port is only reachable if our files
  import it — bridges will. Its 4 sorries make `sorryAx` reachable from any
  bridge that USES gated results — **bridges must consume only the sorry-free
  results** and `#print axioms` every bridge).

## Bridge layer (A4)

Type alignment needed (their parallel definitions vs ours):
- their `Divisor`/divisor arithmetic ↔ our `Divisor X := FreeAbelianGroup X`
- their L(D) (meromorphic functions w/ divisor bound) ↔ our
  `riemannRochSpace D ⊆ MeroField X` (germ quotient!) — the delicate one
- their Čech `H¹(X, 𝒪_D)` model → our `H1coh D` (this is a *definition
  replacement*: `H1coh := (their model)`, then the 3 instances are inherited,
  then `cohomologyLES` is proved from `exists_skyscraperLES` through the
  L(D)-bridge)
- their `genus` (their def) ↔ our `genus = finrank ℂ (HolomorphicOneForm X)`
  — needed only for the keystone-gated pieces; defer.

Faithfulness vetting (A2): per-type DT queries before relying — the port is
AI-produced and unreviewed upstream (their own disclaimer).

## Keystone + period floor (B, C)

- B: `exists_serreDualityData` (§17.5 connecting map + §17.9 surjectivity) —
  THE single chokepoint for full Serre; everything beneath it is proved.
  Coordinate with rkirov upstream (draft issue → MRD approves before posting).
- C: `exists_cutSurface` — discharges `AX_AnalyticCycleBasis` +
  `intersectionForm`+laws and unlocks RBR1/RBR2 (port's bilinear relations
  are proved conditional on it). Pays the "topological anchoring" debt flagged
  in the intersection-form vetting.

## Conformance note (D1)

Upstream targets Buzzard challenge **v0.4** (no `[Nonempty X]`, `𝓘(ℂ,E)`,
universe-polymorphic `Jacobian : Type u`) with a verbatim spec +
`ChallengeConformance.lean` machine-check. We target v0.2. Diff + adopt the
conformance-check pattern.

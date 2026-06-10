# Buzzard challenge spec: v0.2 → v0.4 diff and conformance plan (Task D1)

Date: 2026-06-10. Sources:

- **Our v0.2 target:** `Jacobians/Challenge.lean` (Buzzard's v0.2 statements verbatim,
  24 sorries closed; pinned per `README.md:108`).
- **Verbatim spec revisions:** fetched from the gist
  `kbuzzard/778bc714030b3e974ab5f4038783d1a9` revision history:
  v0.1 `f3fee3cc` (2026-04-19), **v0.2 `5d18a641`** (2026-04-19),
  v0.3 `e554ae34` (2026-04-24), v0.4 `3457be16` + **`cdc146c3`** (both 2026-05-21;
  the second only fixes changelog indentation). Verified byte-identical:
  gist `cdc146c3` == upstream's pinned `Jacobian_challenge.lean` at
  `rkirov/jacobian-claude@4437c2b` (the commit our
  `vendor/kirov-jacobian-claude-dolbeault/` snapshot captures, per its
  `PROVENANCE.md`).
- **Upstream conformance harness:** `Jacobian_challenge.lean` (154 lines) +
  `ChallengeConformance.lean` (109 lines) at `rkirov/jacobian-claude@4437c2b`.
  These two files are **not** in our vendored snapshot (it vendors `Jacobians.lean`
  + `Jacobians/` only); fetched from upstream GitHub at the pinned commit.

---

## 1. Complete v0.2 → v0.4 spec diff

`diff` of gist revisions `5d18a641` (v0.2) vs `cdc146c3` (v0.4). **Every** statement
difference is listed; there are no others.

| # | Delta | v0.2 (spec line) | v0.4 (spec line) | Kind |
|---|-------|------------------|------------------|------|
| 1 | `genus`: drop `[Nonempty X]` | 43–44 | 46–47 | signature (v0.3 change) |
| 2 | `Jacobian`: drop `[Nonempty X]` | 58–59 | 61–62 | signature (v0.3 change) |
| 3 | `Y` variable block: drop `[Nonempty Y]` | 99–100 | 101–102 | signature, propagates into `pushforward`, `pushforward_contMDiff`, `pushforward_id_apply`, `pushforward_comp_apply`, `pullback`, `pullback_contMDiff`, `pullback_id_apply`, `pullback_comp_apply`, `ContMDiff.degree`, `pushforward_pullback` (v0.3 change) |
| 4 | `Z` variable block: drop `[Nonempty Z]` | 117–118 | 118–119 | signature, propagates into `pushforward_comp_apply`, `pullback_comp_apply` (v0.3 change) |
| 5 | Notation `modelWithCornersSelf ℂ E` → `𝓘(ℂ, E)` in 5 statements: the `IsManifold` and `LieAddGroup` instances, `ofCurve_contMDiff`, `pushforward_contMDiff`, `pullback_contMDiff` | 83, 86, 91–92, 111–112, 135–136 | 86, 89, 94, 112–113, 135–136 | **cosmetic only** — `𝓘(𝕜, E)` is Mathlib notation for `modelWithCornersSelf 𝕜 E`; Buzzard's own changelog: "v0.4 is syntactically identical to v0.3" (v0.4 change) |
| 6 | Header Mathlib pin comment: `8e3c989` (2026-04-15) → `5483982` (2026-05-15) | 1 | 1 | comment only |
| 7 | Changelog prose | 32–35 | 33–38 | comment only |

**Important non-deltas** (things that did *not* change v0.2 → v0.4):

- **`Jacobian : Type u` is in BOTH v0.2 and v0.4** (`universe u in … def Jacobian
  (X : Type u) … : Type u`, v0.2 lines 56–59 = v0.4 lines 58–62, unchanged). The
  Phase-D plan's conformance note (`docs/planning/PHASE_D_BRIDGE_PLAN.md:79-84`)
  lists "universe-polymorphic `Jacobian : Type u`" as a v0.4 feature — that is a
  description of what *upstream achieved* (they previously deviated with a `Type 0`
  torus and closed the gap by `ULift`-ing, see their `Jacobians.lean:632-651`), not
  a spec delta. The v0.2 changelog entry "`Type*` not `Type u`" refers to the
  *other* declarations; `Jacobian` itself kept `Type u` in every version.
- All declaration names, all theorem statements (modulo the `[Nonempty]` context
  and the notation), the 7 required instances, `ofCurve_self`, `ofCurve_inj`,
  `genus_eq_zero_iff_homeo`, functoriality lemmas, `g.comp f` vs `g ∘ f`
  spellings — identical.
- The `X` variable block **never had** `[Nonempty X]`, even in v0.2 (it is absent
  from the diff). So v0.2 already relied on Mathlib's `ConnectedSpace → Nonempty`
  instance to elaborate `genus X` inside lemma statements — which is exactly why
  Buzzard could drop the redundant `[Nonempty]`s in v0.3.

---

## 2. What conforming to v0.4 would require of us, per delta

Our `Jacobians/Challenge.lean` preserves the v0.2 statements verbatim (diff against
gist `5d18a641` confirms: only the import header, `noncomputable` markers, closed
proof bodies, and one extra `ConnectedSpace (Jacobian X)` instance at
`Challenge.lean:102-105` differ).

### Deltas 1–4: drop `[Nonempty X/Y/Z]` — *trivial rename-level edit, backward-compatible*

Sites in our file: `Challenge.lean:59` (`genus`), `:79` (`Jacobian`), `:142`
(`[Nonempty Y]`), `:163` (`[Nonempty Z]`). Delete four tokens.

Why it is safe:

- The internal definitions we delegate to **already lack** `[Nonempty _]`:
  `Jacobians.RiemannSurface.genus` (`Jacobians/RiemannSurface/Genus.lean:39-43`)
  and `Jacobians.Jacobian` (`Jacobians/Jacobian/Construction.lean:146-149`). The
  `[Nonempty X]` in `Challenge.lean` is vestigial v0.2 text; the wrapper bodies
  never use it.
- All downstream consumers (`Jacobians/Axioms/TorusAlbanese.lean`,
  `Jacobians/Extensions/{AbelJacobi,HyperellipticEven,HyperellipticOdd}.lean` —
  the only importers of `Jacobians.Challenge`) reach these decls through instance
  synthesis; no `@genus` / `@Jacobian` explicit applications exist anywhere in
  `Jacobians/` (grep verified). Removing an instance-implicit argument that was
  always synthesizable (from `ConnectedSpace.toNonempty`) cannot break such call
  sites.
- Conversely, *keeping* them is also conformant under the example-based machine
  check (§3): in the spec's `[ConnectedSpace _]` context, Lean synthesizes
  `Nonempty` automatically, so `genus X` etc. still elaborate. I.e. deltas 1–4
  affect *verbatim signature equality* but not *example-check conformance*.

**Difficulty: trivial (4-token edit + `lake env lean Jacobians/Challenge.lean`).
Backward-compatible: yes.**

### Delta 5: `𝓘(ℂ, E)` notation — *purely cosmetic, zero semantic change*

Sites in our file using the long form: `Challenge.lean:115-118` (`IsManifold`
instance), `:121-124` (`LieAddGroup` instance), `:130-131` (`ofCurve_contMDiff`),
`:153-155` (`pushforward_contMDiff`), `:181-182` (`pullback_contMDiff`). Rewrite
to `𝓘(ℂ, Fin (genus X) → ℂ)` etc. The notation elaborates to the identical term
(`modelWithCornersSelf`), so nothing downstream can notice; the `change` tactics
inside those instance bodies keep working.

**Difficulty: trivial. Backward-compatible: yes (statements are definitionally and
syntactically-post-elaboration identical).**

### Delta 6: Mathlib pin — *no action*

v0.4 says "compiles with `5483982` (2026-05-15)". We pin `c5ea0035` (2026-05-26,
v4.30.0), which is newer; our file already compiles. The pin comment in the spec
header is informational, not a conformance requirement.

### Non-delta: `Jacobian : Type u` — *already conformant*

`Challenge.lean:75-80` signs `Jacobian (X : Type u) : Type u`, backed by
`Jacobians.Jacobian X = ULift.{u,0} (JacobianAmbient X)`
(`Jacobians/Jacobian/Construction.lean:146-149`) with all seven instances
transported through the ULift (same architectural solution upstream adopted later
in their `ULiftManifold`). Nothing to do.

### Summary

**Conforming to v0.4 is a one-file, ~10-line cosmetic edit to
`Jacobians/Challenge.lean`; no real math, no internal API changes, fully
backward-compatible.** Our current v0.2-shaped interface would in fact already
pass upstream's example-based v0.4 conformance check unmodified (the `[Nonempty]`
arguments are synthesized away); the edit is only needed for strict
"same-signature" conformance and for keeping our pinned copy honest if we relabel
it v0.4.

---

## 3. Upstream's `ChallengeConformance.lean` machine-check pattern

How `rkirov/jacobian-claude@4437c2b` pins and checks the spec (precise enough to
replicate):

1. **Pin the spec verbatim.** `Jacobian_challenge.lean` (repo root, 154 lines) is
   a byte-for-byte copy of the gist's v0.4 revision, including `import Mathlib`,
   docstrings, and all 24 `sorry`s. It sits at the repo root *outside* the
   `Jacobians` lib source dir, so `lake build` never compiles it (it would emit 24
   sorry warnings); it serves as the immutable reference text. (Verified: gist
   `cdc146c3` and their file are identical.)

2. **Conformance file = spec restated as `example`s.** `ChallengeConformance.lean`
   (repo root, 109 lines) has the shape:
   - `import Jacobians` (the implementation), `open scoped ContDiff` /
     `open scoped Manifold`, `universe u`, then **one `noncomputable section`
     wrapping the whole file** (the data decls are noncomputable and only type
     inhabitation matters, not code generation).
   - The spec's `variable` blocks are copied **verbatim** (same binders, same
     typeclass lists — no `[Nonempty _]`), recreating the exact elaboration
     context of each spec statement.
   - For each of the 24 spec declarations there is one anonymous `example`
     restating the v0.4 type **verbatim** and discharging it with the
     implementation's declaration:
     - data defs: term-mode, e.g. `example … : Type u := Jacobian X`,
       `example (P : X) : X → Jacobian X := ofCurve P`;
     - the 7 instances: `example : AddCommGroup (Jacobian X) := inferInstance` …;
     - lemmas: direct term application (`:= ofCurve_inj P h`) where unification
       is immediate, or `:= by apply pushforward_comp_apply` where the statement
       contains defs (`pushforward (g ∘ f) …`) whose unfolding `apply` handles
       better than first-order unification;
     - namespacing mirrors the spec (`namespace Jacobian … end Jacobian`).
   - Because each `example` *restates the spec type* rather than `#check`ing the
     implementation, the kernel verifies that the implementation's type unifies
     with the verbatim spec type under exactly the spec's typeclass context —
     names, binder structure, and statements all checked at once.
   - Universe polymorphism is pinned by giving the `Jacobian` example an explicit
     `(X : Type u)` binder against the file-level `universe u`.

3. **Run it.** `lake env lean ChallengeConformance.lean` (after `lake build`), exit
   0 = conformance. Their README (`vendor/kirov-jacobian-claude-dolbeault/README.md:70`)
   documents it as a first-class verification step alongside `lake build`.

   Limit of the check (their README is explicit about this, lines 40–44): an
   `example` discharged by a declaration whose proof still contains `sorry`
   compiles fine — conformance certifies *signatures*, not sorry-freeness; that is
   what `#print axioms` / our axiom-report CI gate is for.

### Replication recipe for our repo

- Add `Jacobian_challenge_v0_4.lean` at repo root (or under `vendor/buzzard-gist/`)
  — byte-identical to gist revision `cdc146c3fd…` (save it with provenance note:
  gist URL + revision SHA + date). Not in the build root.
- Add `ChallengeConformance.lean` at repo root: since our root-level names
  (`genus`, `Jacobian`, `Jacobian.ofCurve`, …) coincide with upstream's, their
  conformance file works for us almost verbatim — replace the header comment and
  keep Apache-2.0 attribution per our vendoring policy (`CLAUDE.md` §Vendored
  material), or write it fresh from the spec (it is mechanical).
- CI: append a step to `.github/workflows/lean.yml` after `lake build`:
  `lake env lean ChallengeConformance.lean`. (Workflow edits are owner-vetted via
  CODEOWNERS.) Cost: seconds, since `lake build` has already produced the oleans.
- Optionally keep a second conformance file for v0.2 (gist `5d18a641`) while
  `Challenge.lean` still carries the v0.2 shape, so the README claim "v0.2
  verbatim" is machine-checked too.

---

## 4. Recommendation

| Delta | Action | Effort |
|---|---|---|
| 1–4 `[Nonempty]` drops | **Adopt** (4-token edit in `Challenge.lean` + relabel header v0.2→v0.4 + update changelog block + README) | minutes |
| 5 `𝓘(ℂ, E)` notation | **Adopt** (cosmetic, same commit) | minutes |
| 6 Mathlib pin comment | No action (we are newer) | — |
| `Type u` Jacobian | Already conformant | — |
| Conformance harness | **Adopt** upstream's pattern: pin gist `cdc146c3` verbatim + `ChallengeConformance.lean` + CI step | ~30 min (CI edit needs owner review) |

There is no blocking item and no real mathematics in the v0.2→v0.4 gap; a single
small PR (Challenge.lean edit + verbatim spec pin + conformance file + CI step)
makes us strictly v0.4-conformant with a machine check, and removes the spec-version
skew between us and upstream `rkirov/jacobian-claude`.

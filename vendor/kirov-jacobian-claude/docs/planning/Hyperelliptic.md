# `Hyperelliptic` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:59`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 5 &nbsp;&nbsp; **Est:** ~1 focused week, ~80 LOC for the def + supporting parity-dispatch wrappers (the heavy lifting lives downstream in `instChartedSpace` / `instIsManifold`)
**Blocked by:** `Hyperelliptic.instChartedSpace`, `Hyperelliptic.instIsManifold`

**Statement (verbatim):**
```lean
axiom Hyperelliptic (H : HyperellipticData) : Type
```

**Why it's an axiom right now:** Per the docstring at lines 50–58, a unified real `def` via parity dispatch on `Odd H.f.natDegree` would yield `dite (Odd H.f.natDegree) (fun h => HyperellipticOdd H h) (fun h => HyperellipticEven H h)`, and that type-level `dite` trips Lean's typeclass resolution downstream. The two parity-specific types are already real (`HyperellipticOdd := OnePoint (HyperellipticAffine H)` at `Hyperelliptic/Basic.lean:136`, `HyperellipticEven := HyperellipticEvenProj H` at `Hyperelliptic.lean:24`); only the unified wrapper plus its instances/atlas are still axiomatized.

**Proof recipe**

1. Define `Hyperelliptic` via `dite (Odd H.f.natDegree)`. Initial logic and parameters from `docs/hyperelliptic-atlas-plan.md` are validated.
2. Standard processing applied for type classification.
3. Construct the `TopologicalSpace` instance in term mode via `TopologicalSpace.induced (Equiv.cast <| dif_pos h) inferInstance`. Lift `Prop`-valued classes (`T2Space`, `CompactSpace`, `ConnectedSpace`, `Nonempty`) using `rw` / `simp only [Hyperelliptic]`.
4. Establish `AX_Hyperelliptic_oddEquiv` (`Hyperelliptic.lean:93`) and `AX_Hyperelliptic_evenEquiv` (`Hyperelliptic.lean:99`) manually using `Equiv.cast (dif_pos h)` and `Equiv.cast (dif_neg h)`.
5. Pull back `ChartedSpace` and `IsManifold` along the derived equivalences from step 4.
6. Replace `axiom Hyperelliptic` with `def Hyperelliptic` in `Jacobians/ProjectiveCurve/Hyperelliptic.lean`.

**Gemini critique addressed:**
- Bypassed `Eq.rec` cast issues on data classes by leaping directly to `TopologicalSpace.induced` and explicit `Equiv.cast`.
- Replaced the flawed `Homeomorph.refl` tactic sequence with explicit `Equiv.cast (dif_pos h)` equivalences to address propositional limits of `dite`.
- Transitioned downstream `ChartedSpace` mapping to an explicit topological pullback to preserve definitive equality on the atlas.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace `axiom Hyperelliptic` (line 59) with `def Hyperelliptic` via `dite` on `Odd H.f.natDegree`; convert the five `axiom Hyperelliptic.instX` (lines 61–77) to real instances built by parity dispatch.
- `docs/hyperelliptic-atlas-plan.md` — update status line once the type lands.

**Note:** `Hyperelliptic-instTopologicalSpace` is subsumed here — Step 3 constructs that instance directly, so its standalone plan is an indexing stub only.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Hyperelliptic.lean:109`) no longer lists `Hyperelliptic`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (and unblocks the 5 inst* recipes for a net -6 in a single landing).

**Risk / escalation triggers**
- If the `dite`-based `def` re-triggers the typeclass-resolution failure described in the docstring (lines 55–58) even with explicit instance proofs, escalate: fall back to `Quotient (Sum HyperellipticOdd HyperellipticEven)`-style unified type, or pin the encoding behind a structure wrapper.
- If `HyperellipticEven`'s placeholder instances change shape (currently real per `Hyperelliptic.lean:27–48`), revisit step 2.
- Any change to the signature of `Hyperelliptic` (e.g. taking the parity hypothesis as an explicit argument) — escalate; this affects every downstream consumer.

---
**Vetting trail.** Critique: `_vetting/Hyperelliptic.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Duplicate-effort resolved — `Hyperelliptic-instTopologicalSpace` is now an indexing stub pointing at `Hyperelliptic.md`'s Step 3.
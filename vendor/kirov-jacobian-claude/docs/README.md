# docs/ — index

Design + research notes for the Jacobians challenge. For the authoritative *code* state always prefer
`git grep -nE ':= *sorry'` — prose status docs lag the tree.

## Start here

| Doc | What it is |
|---|---|
| **[path_to_completion_reuse.md](path_to_completion_reuse.md)** | **The live, authoritative doc.** Maximal-reuse audit of the whole path: the 5 walls, what's done / assembly / genuine-new, the `ω₀` keystone (no Hodge wall), and the maximal-reuse plan. |
| [architecture_map.md](architecture_map.md) | Dependency DAG to a sorry-free finish. (`architecture_map.html`, gitignored, is the visual version.) |
| [STATUS.md](STATUS.md) | Wall-by-wall status table. Lags the tree — verify against `git grep sorry`. |

## Foundations

| Doc | What it is |
|---|---|
| [DESIGN.md](DESIGN.md) | Construction choices (period-lattice Jacobian, topological genus, deferrals). |
| [REFERENCES.md](REFERENCES.md) | Canonical textbooks/papers (Forster GTM 81, Miranda, …). |

## Per-wall research (reference detail behind the synthesis)

| Wall | Doc |
|---|---|
| **W1 RR/Serre** (make-or-break) | [hodge_bridge_research.md](hodge_bridge_research.md) (the §17 Serre pairing), [cech_finiteness_research.md](cech_finiteness_research.md) (H¹ finiteness, Forster 14.9) |
| **W2 deg_div** | [deg_div_research.md](deg_div_research.md) (degree route; argument-principle atom) |
| **W3 #7 period lattice** | [period_lattice_realbasis_research.md](period_lattice_realbasis_research.md) |
| **W4 #3 Abel** | [abel_riemannroch_research.md](abel_riemannroch_research.md) |

## Archive (`archive/`) — superseded / historical, kept for provenance

Synthesized into `path_to_completion_reuse.md` or describing work now done. Not load-bearing.

- **Superseded plans:** `riemann_roch_proof_plan.md`, `dolbeault_ladder_derisk.md`,
  `dolbeault_disk_atom_decomposition.md`, `dolbeault_comparison_forward_plan.md`,
  `dolbeault_comparison_inverse_plan.md`, `dolbeault_hodge_feasibility.md`, `period_realbasis_plan.md`,
  `genus_endgame_wiring_plan.md`, `trace_branchpoint_plan.md`, `preimage_cycle_lift_plan.md`,
  `S8_TRACE_PLAN.md`.
- **Recon (complete):** `EXTERNAL_AUDIT.md` (brsanch port + mrdouglasny vendoring),
  `loop_off_branch_research.md` (#6).

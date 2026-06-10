import Lake
open Lake DSL

package jacobian where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c5ea00351c28e24afc9f0f84379aa41082b1188f"

@[default_target]
lean_lib KirovDolbeault where
  -- Build *every* module under `KirovDolbeault/`, not just those reachable
  -- from the `KirovDolbeault.lean` root. Without this, orphan modules (probes /
  -- in-progress endgames not yet wired into the challenge aggregator) are
  -- skipped by `lake build`, which once let a RED commit sit undetected on
  -- `main`.
  globs := #[.andSubmodules `KirovDolbeault]
  -- Port of rkirov/jacobian-claude@4437c2b to Mathlib c5ea003 (v4.30.0).
  -- S2 integration (docs/planning/PHASE_D_BRIDGE_PLAN.md): module root renamed
  -- Jacobians → KirovDolbeault so the port can coexist with the parent
  -- package's `Jacobians` lib as a Lake path dependency. Declaration names
  -- (namespace `Jacobians.*`) are unchanged from upstream.

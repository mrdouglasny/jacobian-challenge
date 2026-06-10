import Lake
open Lake DSL

package jacobian where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "8e3c989104daaa052921bf43de9eef0e1ac9fbf5"

@[default_target]
lean_lib Jacobians where
  -- Build *every* module under `Jacobians/`, not just those reachable from the
  -- `Jacobians.lean` root. Without this, orphan modules (probes / in-progress
  -- endgames not yet wired into the challenge aggregator) are skipped by
  -- `lake build`, which once let a RED commit sit undetected on `main`.
  globs := #[.andSubmodules `Jacobians]

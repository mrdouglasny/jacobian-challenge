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

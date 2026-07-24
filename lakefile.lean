import Lake
open Lake DSL

package «collision-ideals» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
    "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib CollisionIdeals

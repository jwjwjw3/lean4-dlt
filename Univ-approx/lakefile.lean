import Lake
open Lake DSL

package univapprox where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib UnivApprox where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.15.0"

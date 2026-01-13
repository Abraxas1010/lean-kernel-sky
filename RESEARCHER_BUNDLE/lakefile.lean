import Lake
open Lake DSL

package «HeytingLean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib «HeytingLean» where
  globs := #[.submodules `HeytingLean]

lean_exe lean4lean_sky_demo where
  root := `HeytingLean.CLI.Lean4LeanSKYMain

lean_exe kernel_sky_demo where
  root := `HeytingLean.CLI.KernelSKYMain

lean_exe full_kernel_sky_demo where
  root := `HeytingLean.CLI.FullKernelSKYMain

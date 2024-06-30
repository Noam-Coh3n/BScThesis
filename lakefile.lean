import Lake
open Lake DSL

package «cyclic_formulas» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «CyclicFormulas» where
  -- add any library configuration options here

@[default_target]
lean_exe «cyclic_formulas» where
  root := `Main
  supportInterpreter := true
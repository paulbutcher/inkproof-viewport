/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-viewport» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «inkproof-scale» from git "https://github.com/paulbutcher/inkproof-scale" @ "v0.6.0"
require «inkproof-float» from git "https://github.com/paulbutcher/inkproof-float" @ "v0.5.0"

@[default_target]
lean_lib InkproofViewport where
  roots := #[`Inkproof.Viewport, `Inkproof.Viewport.Proofs]

@[test_driver]
script tests do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait

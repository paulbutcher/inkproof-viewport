/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport
import InkproofTools.Test.Platform
import InkproofViewportTest.ViewTests

open InkproofViewportTest InkproofTools.Test

def main (args : List String) : IO UInt32 :=
  runTests (platformTest (args.contains "--expect-wasm") :: ViewTests.tests)

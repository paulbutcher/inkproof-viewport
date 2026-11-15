/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport
import InkproofTools.Test.Harness

/-! Float views driven by inputs: the proved properties hold up to rounding, and the pieces
(linked views, events) behave together. -/

namespace InkproofViewportTest.ViewTests

open InkproofTools.Test
open Inkproof.Viewport

def intervalConfig : Interval.Config Float :=
  { length := 800, minSpan := 0.5, maxSpan := 1000, home := ⟨0, 100⟩, keyZoom := 1.25, keyPan := 0.1 }

def config : ViewConfig Float := ⟨intervalConfig, intervalConfig⟩

def near (a b : Float) : Bool := (a - b).abs ≤ 1e-6 * (1 + a.abs + b.abs)

/-- Inputs of every kind from a stream of numbers, including ones outside any limits. -/
def inputOf (k : Nat) (a b c d : Float) : Input Float :=
  match k % 7 with
  | 0 => .wheel a b (c / 100 - 2)
  | 1 => .pinch a b (c / 100) (d / 100)
  | 2 => .drag (a - 400) (b - 400)
  | 3 => .key (match k / 7 % 6 with
      | 0 => .zoomIn | 1 => .zoomOut | 2 => .left | 3 => .right | 4 => .up | _ => .down)
  | 4 => .box a b c d
  | 5 => .set (a - 500) (b - 500) (c - 500) (d - 500)
  | _ => .reset

def sequence (n : Nat) (seed : Nat) : List (Input Float) :=
  (List.range n).map fun j =>
    let s := seed * 31 + j * 17
    inputOf s (s % 800).toFloat (s / 3 % 800).toFloat (s / 5 % 400).toFloat (s / 7 % 400).toFloat

def run (inputs : List (Input Float)) : View Float :=
  inputs.foldl (View.step config) (View.home config)

def limitsHold : TestCase := .mk "Zoom limits hold after any sequence of inputs" <|
  forAll 300 (fun g =>
    let (n, g) := g.below 30
    let (seed, g) := g.below 100000
    ((n, seed), g)) fun (n, seed) => do
    let v := run (sequence n seed)
    check (intervalConfig.minSpan ≤ v.x.span && v.x.span ≤ intervalConfig.maxSpan) "x span out of limits"
    check (intervalConfig.minSpan ≤ v.y.span && v.y.span ≤ intervalConfig.maxSpan) "y span out of limits"

def zoomKeepsPoint : TestCase := .mk "A wheel zoom keeps the data under the pointer" <|
  forAll 300 (fun g =>
    let (n, g) := g.below 15
    let (seed, g) := g.below 100000
    let (p, g) := g.below 800
    let (f, g) := g.below 300
    ((n, seed, p, f), g)) fun (n, seed, p, f) => do
    let v := run (sequence n seed)
    let w := View.step config v (.wheel p.toFloat p.toFloat (f.toFloat / 100 + 0.1))
    check (near (View.cursor config v p.toFloat 0).1 (View.cursor config w p.toFloat 0).1)
      "data under the pointer moved"

def linkedAgree : TestCase := .mk "Views linked on x agree after an input to either" <|
  forAll 300 (fun g =>
    let (n, g) := g.below 20
    let (seed, g) := g.below 100000
    ((n, seed), g)) fun (n, seed) => do
    let g0 : Linked Float 2 := ⟨⟨⟨0, 100⟩⟩, fun _ => ⟨0, 100⟩⟩
    let mut g1 := g0
    let mut j := 0
    for i in sequence n seed do
      g1 := g1.step config (if j % 2 == 0 then 0 else 1) i
      j := j + 1
    check ((g1.view 0).x == (g1.view 1).x) "x axes differ"

def eventsReplay : TestCase := .mk "Applying emitted events reproduces the view" <|
  forAll 300 (fun g =>
    let (n, g) := g.below 20
    let (seed, g) := g.below 100000
    ((n, seed), g)) fun (n, seed) => do
    let mut mine := View.home config
    let mut remote := View.home config
    for i in sequence n seed do
      let (v, e) := View.stepEvent config mine i
      mine := v
      if let some e := e then remote := remote.receive e
    check (mine == remote) "replayed view differs"

def tests : List TestCase := [limitsHold, zoomKeepsPoint, linkedAgree, eventsReplay]

end InkproofViewportTest.ViewTests

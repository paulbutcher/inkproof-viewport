# Inkproof.Viewport

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

A view is the visible range of each axis, as a pure state machine: `View.step` takes a view and an input (wheel, pinch, drag, key, box zoom, programmatic set, reset) and gives the next view, with zoom limits. Views can share an axis (`Linked`), the cursor's data position is the inverse of the view's transform, and `View.stepEvent` yields a `ViewChange` for a host to forward. Everything is generic over the number type; the theorems are over ordered fields, and `Float` is used at run time.

## What it does

- Step a view (x and y ranges) by an input event, with zoom limits: `View.step`, `Input` (wheel, pinch, drag, key, box zoom, set, reset), `View.home`, `ViewConfig`; one axis alone: `Interval.zoomAt`, `Interval.pan`, `Interval.drag`, `Interval.box`, `Interval.fit`, `Interval.clampSpan`, `Interval.Config`.
- Convert between data and screen positions, including the cursor's data position: `Interval.toScreen`, `Interval.toData`, `View.toScreen`, `View.cursor`, `Interval.toLinear`.
- Convert pointer gestures to inputs over a `ViewConfig`: wheel delta to zoom factor, two-finger pinch to pinch and drag inputs, box drag to a box input, screen to view position, and whether a position is over the plot: `Gesture.wheelFactor`, `Gesture.spread`, `Gesture.pinch`, `Gesture.box`, `Gesture.toView`, `Gesture.inside`.
- Find which samples of a recording a visible range touches: `Interval.indexRange`.
- Link views so they share an axis, with per-view unlink and relink: `Linked`, `Linked.step`, `Linked.view`, `Linked.unlink`, `Linked.relink`.
- Forward view changes to a host or another user, apply received ones, and prove a view stays within its limits: `View.stepEvent`, `ViewChange`, `View.receive`, `View.Within`, `View.Reachable`, `View.step_within`.

## Using it

Add to your `lakefile.lean`:

```lean
require «inkproof-viewport» from git "https://github.com/paulbutcher/inkproof-viewport" @ "v0.4.1"
```

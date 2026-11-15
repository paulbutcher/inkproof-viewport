# Inkproof.Viewport

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

A view is the visible range of each axis, as a pure state machine: `View.step` takes a view and an input (wheel, pinch, drag, key, box zoom, programmatic set, reset) and gives the next view, with zoom limits. Views can share an axis (`Linked`), the cursor's data position is the inverse of the view's transform, and `View.stepEvent` yields a `ViewChange` for a host to forward. Everything is generic over the number type; the theorems are over ordered fields, and `Float` is used at run time.

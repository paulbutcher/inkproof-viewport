# Changelog

## v0.5.1

Tests use `Float.near` from inkproof-float v0.6.0.

## v0.5.0

`Interval.indexRange` gives the non-empty range of sample indices an interval touches in a recording of `n` samples.

## v0.4.1

Tests run under @lasm/cli 0.8.0.

## v0.4.0

A view in `Linked` can be unlinked from the shared x axis and relinked to it; breaking, as `Linked` gains a field and the link theorems now name the linked views.

## v0.3.0

Uses `Inkproof.Float.clamp` in place of `Interval.clamp`, which is removed; breaking.

## v0.2.0

Renamed `Axis` to `Interval` (and `Axis.Config` to `Interval.Config`) so it no longer collides with the Inkproof.Axis namespace; breaking.

## v0.1.0

The view state machine with zoom limits, linked views sharing an axis, cursor position and view-change events, with proofs.

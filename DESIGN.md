# Inkproof.Viewport design

## State

An `Axis` is a start and a span in data units; its screen length, zoom limits, home view and key steps are an `Axis.Config`. Its transform to the screen is a Scale `Linear`, so the cursor is `Linear.inv.map` and inverts it by Scale's theorems. A `View` is an x and a y `Axis`.

## Step

`View.step` is total: every input, including a non-positive zoom factor, gives a view. A factor that is not positive (NaN included) is ignored. Spans are clamped to the limits after every zoom, box zoom or programmatic set, so `View.Within` holds in every reachable state when the configuration is `Valid` (positive length and minimum span, limits in order, home within them). Hosts convert a wheel notch or pinch to a factor, which keeps the machine independent of timing and platform.

## Proofs

Theorems are over a field with a linear order, so they cover exact arithmetic; `Float` is not one. Hosts using `Float` must keep non-finite values out of inputs. Zoom in then out restores the view only when the zoomed-in span is within the limits, since a clamp loses information; the theorem states that hypothesis, which a caller meets by choosing the factor.

## Linked views

`Linked` holds the shared x axis once as a Scale `Shared`, so views agree by construction (VIEW-3). An input to one view updates the shared axis and that view's y axis.

## Events

`stepEvent` yields a `ViewChange` carrying the new view when a step changes it. `receive` applies one without producing another, so forwarding cannot echo. How events travel is the host's concern (VIEW-4).

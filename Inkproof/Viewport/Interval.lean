/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale

universe u

namespace Inkproof.Viewport

/-- The visible range of one axis: the data interval from `start` to `start + span`, shown over
the screen interval from `0` to the axis's `length`. -/
structure Interval (α : Type u) where
  start : α
  span : α
  deriving Repr, BEq, ReflBEq, LawfulBEq

namespace Interval

/-- What fixes an axis's behaviour: its screen `length`, the zoom limits on the visible span, the
view `reset` returns to, the zoom factor of one keyboard step and the fraction of the span panned
by one. `Valid` says when these make sense. -/
structure Config (α : Type u) where
  length : α
  minSpan : α
  maxSpan : α
  home : Interval α
  keyZoom : α
  keyPan : α
  deriving Repr

variable {α : Type u}

/-- The span lies within the zoom limits. -/
def Within [LE α] (c : Config α) (a : Interval α) : Prop := c.minSpan ≤ a.span ∧ a.span ≤ c.maxSpan

/-- A positive screen length, positive limits in order, and a home view within them. Zoom and pan
are total without this, but the theorems about them need it. -/
def Config.Valid [OfNat α 0] [LE α] [LT α] (c : Config α) : Prop :=
  0 < c.length ∧ 0 < c.minSpan ∧ c.minSpan ≤ c.maxSpan ∧ Within c c.home

/-- `x` held to the interval from `lo` to `hi`. -/
def clamp [LT α] [DecidableLT α] (lo hi x : α) : α :=
  if x < lo then lo else if hi < x then hi else x

/-- The transform from data to screen; its inverse is the cursor's. -/
def toLinear [Add α] [OfNat α 0] (c : Config α) (a : Interval α) : Scale.Linear α :=
  ⟨a.start, a.start + a.span, 0, c.length⟩

/-- The screen position of a data value. -/
def toScreen [Add α] [Sub α] [Mul α] [Div α] [OfNat α 0] (c : Config α) (a : Interval α) (d : α) : α :=
  (toLinear c a).map d

/-- The data value at a screen position. -/
def toData [Add α] [Sub α] [Mul α] [Div α] [OfNat α 0] (c : Config α) (a : Interval α) (p : α) : α :=
  (toLinear c a).inv.map p

/-- A span held to the zoom limits. -/
def clampSpan [LT α] [DecidableLT α] (c : Config α) (s : α) : α := clamp c.minSpan c.maxSpan s

/-- Zoom in by factor `f` about the screen position `p`, so the data under `p` stays under it.
A factor that is not positive, which includes NaN, leaves the view alone. -/
def zoomAt [Add α] [Sub α] [Mul α] [Div α] [OfNat α 0] [LT α] [DecidableLT α] (c : Config α)
    (a : Interval α) (p f : α) : Interval α :=
  if 0 < f then
    let s := clampSpan c (a.span / f)
    ⟨toData c a p - p * s / c.length, s⟩
  else a

/-- Shift the view by `d` in data units. -/
def pan [Add α] (a : Interval α) (d : α) : Interval α := ⟨a.start + d, a.span⟩

/-- Drag the content by `dp` screen units. -/
def drag [Add α] [Mul α] [Div α] [Neg α] (c : Config α) (a : Interval α) (dp : α) : Interval α :=
  pan a (-(dp * a.span / c.length))

/-- The view showing the data interval between `d₀` and `d₁`, in either order, widened about its
centre if the zoom limits demand. -/
def fit [Add α] [Sub α] [Div α] [OfNat α 1] [LT α] [DecidableLT α] (c : Config α) (d₀ d₁ : α) :
    Interval α :=
  let lo := if d₁ < d₀ then d₁ else d₀
  let raw := if d₁ < d₀ then d₀ - d₁ else d₁ - d₀
  let s := clampSpan c raw
  ⟨lo - (s - raw) / (1 + 1), s⟩

/-- Zoom to the data between the screen positions `p₀` and `p₁`. -/
def box [Add α] [Sub α] [Mul α] [Div α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
    (c : Config α) (a : Interval α) (p₀ p₁ : α) : Interval α :=
  fit c (toData c a p₀) (toData c a p₁)

end Interval

end Inkproof.Viewport

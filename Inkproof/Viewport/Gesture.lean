/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.View

namespace Inkproof.Viewport

/-- A position in pixels from the plot's top left, as a pointer event reports it. -/
abbrev Px := Float × Float

namespace Gesture

/-- The view's screen position for a position in the element: y grows upward in a view and downward on the page. -/
def toView (c : ViewConfig Float) (p : Px) : Px := (p.1, c.y.length - p.2)

theorem toView_eq (c : ViewConfig Float) (p : Px) : toView c p = (p.1, c.y.length - p.2) := rfl

/-- Whether a position lies over the plot, which is what a view's axes span. -/
def inside (c : ViewConfig Float) (p : Px) : Bool :=
  0 ≤ p.1 && p.1 ≤ c.x.length && 0 ≤ p.2 && p.2 ≤ c.y.length

theorem inside_eq (c : ViewConfig Float) (p : Px) :
    inside c p = (0 ≤ p.1 && p.1 ≤ c.x.length && 0 ≤ p.2 && p.2 ≤ c.y.length) := rfl

/-- The zoom factor of a wheel turn of `delta` pixels; scrolling down zooms out. -/
def wheelFactor (delta : Float) : Float := Float.exp (-delta / 500)

theorem wheelFactor_eq (delta : Float) : wheelFactor delta = Float.exp (-delta / 500) := rfl

/-- The factor by which two fingers have moved apart along one axis, or none when either gap is too small to measure. -/
def spread (old new : Float) : Float := if old < 1 || new < 1 then 1 else new / old

theorem spread_eq (old new : Float) : spread old new = if old < 1 || new < 1 then 1 else new / old := rfl

/-- The inputs for two fingers moving from `o₁ o₂` to `n₁ n₂`: zoom about the old midpoint by how far they spread on each axis, then drag by how far the midpoint moved. Positions are already in view coordinates. -/
def pinch (o₁ o₂ n₁ n₂ : Px) : List (Input Float) :=
  let ox := (o₁.1 + o₂.1) / 2
  let oy := (o₁.2 + o₂.2) / 2
  [.pinch ox oy (spread (o₂.1 - o₁.1).abs (n₂.1 - n₁.1).abs) (spread (o₂.2 - o₁.2).abs (n₂.2 - n₁.2).abs),
   .drag ((n₁.1 + n₂.1) / 2 - ox) ((n₁.2 + n₂.2) / 2 - oy)]

theorem pinch_eq (o₁ o₂ n₁ n₂ : Px) :
    pinch o₁ o₂ n₁ n₂ =
      [.pinch ((o₁.1 + o₂.1) / 2) ((o₁.2 + o₂.2) / 2) (spread (o₂.1 - o₁.1).abs (n₂.1 - n₁.1).abs)
        (spread (o₂.2 - o₁.2).abs (n₂.2 - n₁.2).abs),
       .drag ((n₁.1 + n₂.1) / 2 - (o₁.1 + o₂.1) / 2) ((n₁.2 + n₂.2) / 2 - (o₁.2 + o₂.2) / 2)] := rfl

/-- A box drag shorter than this, in pixels, on either axis is a click, not a selection. -/
def minBox : Float := 4

/-- The box zoom for a drag between two positions, if it is big enough. -/
def box (c : ViewConfig Float) (a b : Px) : Option (Input Float) :=
  if (b.1 - a.1).abs < minBox || (b.2 - a.2).abs < minBox then none
  else
    let a := toView c a
    let b := toView c b
    some (.box a.1 a.2 b.1 b.2)

theorem box_eq (c : ViewConfig Float) (a b : Px) :
    box c a b =
      if (b.1 - a.1).abs < minBox || (b.2 - a.2).abs < minBox then none
      else some (.box (toView c a).1 (toView c a).2 (toView c b).1 (toView c b).2) := rfl

theorem box_none (c : ViewConfig Float) (a b : Px) (h : (b.1 - a.1).abs < minBox) : box c a b = none := by
  simp [box, h]

theorem box_some (c : ViewConfig Float) (a b : Px) (h : ¬((b.1 - a.1).abs < minBox || (b.2 - a.2).abs < minBox) = true) :
    box c a b = some (.box (toView c a).1 (toView c a).2 (toView c b).1 (toView c b).2) := by
  simp [box, h]

/-- The axes a box zoom covers; `auto` covers whichever side of the drag is longer, `x` on a tie. -/
inductive Axes where
  | x | y | both | auto

/-- Whether a drag of `dx` by `dy` pixels covers the x axis and the y axis. -/
def Axes.covers : Axes → Float → Float → Bool × Bool
  | .x, _, _ => (true, false)
  | .y, _, _ => (false, true)
  | .both, _, _ => (true, true)
  | .auto, dx, dy => (dy ≤ dx, dx < dy)

theorem Axes.covers_x (dx dy : Float) : Axes.x.covers dx dy = (true, false) := rfl

theorem Axes.covers_y (dx dy : Float) : Axes.y.covers dx dy = (false, true) := rfl

theorem Axes.covers_both (dx dy : Float) : Axes.both.covers dx dy = (true, true) := rfl

theorem Axes.covers_auto (dx dy : Float) : Axes.auto.covers dx dy = (decide (dy ≤ dx), decide (dx < dy)) := rfl

/-- The box zoom for a drag between two positions over the given axes, refused if the drag is shorter than `minDrag` along a covered axis. An axis not covered is spanned by the whole plot, so it keeps its range. -/
def boxOver (c : ViewConfig Float) (axes : Axes) (minDrag : Float) (a b : Px) : Option (Input Float) :=
  let dx := (b.1 - a.1).abs
  let dy := (b.2 - a.2).abs
  let cov := axes.covers dx dy
  if (cov.1 && dx < minDrag) || (cov.2 && dy < minDrag) then none
  else
    let a := toView c a
    let b := toView c b
    some (.box (if cov.1 then a.1 else 0) (if cov.2 then a.2 else 0)
      (if cov.1 then b.1 else c.x.length) (if cov.2 then b.2 else c.y.length))

theorem boxOver_eq (c : ViewConfig Float) (axes : Axes) (minDrag : Float) (a b : Px) :
    boxOver c axes minDrag a b =
      if ((axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).1 && (b.1 - a.1).abs < minDrag) ||
          ((axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).2 && (b.2 - a.2).abs < minDrag) then none
      else
        some (.box (if (axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).1 then (toView c a).1 else 0)
          (if (axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).2 then (toView c a).2 else 0)
          (if (axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).1 then (toView c b).1 else c.x.length)
          (if (axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).2 then (toView c b).2 else c.y.length)) := rfl

theorem box_eq_boxOver (c : ViewConfig Float) (a b : Px) : box c a b = boxOver c .both minBox a b := by
  simp [box, boxOver, Axes.covers]

theorem boxOver_none_x (c : ViewConfig Float) (axes : Axes) (minDrag : Float) (a b : Px)
    (h : (axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).1 = true) (hd : (b.1 - a.1).abs < minDrag) :
    boxOver c axes minDrag a b = none := by
  simp [boxOver, h, hd]

theorem boxOver_none_y (c : ViewConfig Float) (axes : Axes) (minDrag : Float) (a b : Px)
    (h : (axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).2 = true) (hd : (b.2 - a.2).abs < minDrag) :
    boxOver c axes minDrag a b = none := by
  simp [boxOver, h, hd]

/-- An axis not covered gets the whole plot's extent. -/
theorem boxOver_uncovered_x (c : ViewConfig Float) (axes : Axes) (minDrag : Float) (a b : Px) (i : Input Float)
    (hi : boxOver c axes minDrag a b = some i)
    (h : (axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).1 = false) :
    ∃ y₀ y₁, i = .box 0 y₀ c.x.length y₁ := by
  simp only [boxOver, h] at hi
  split at hi <;> simp_all
  subst hi; exact ⟨_, _, rfl⟩

theorem boxOver_uncovered_y (c : ViewConfig Float) (axes : Axes) (minDrag : Float) (a b : Px) (i : Input Float)
    (hi : boxOver c axes minDrag a b = some i)
    (h : (axes.covers (b.1 - a.1).abs (b.2 - a.2).abs).2 = false) :
    ∃ x₀ x₁, i = .box x₀ 0 x₁ c.y.length := by
  simp only [boxOver, h] at hi
  split at hi <;> simp_all
  subst hi; exact ⟨_, _, rfl⟩

end Gesture

end Inkproof.Viewport

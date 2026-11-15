/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.Event
import Inkproof.Viewport.Linked
import Inkproof.Viewport.Proofs.Interval

universe u

namespace Inkproof.Viewport

open Lean.Grind

variable {α : Type u} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α]
  [OrderedRing α] [DecidableLT α]

namespace View

omit [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] [DecidableLT α] in
theorem home_within {c : ViewConfig α} (hc : c.Valid) : Within c (home c) :=
  ⟨hc.1.2.2.2, hc.2.2.2.2⟩

/-- PROOF-9: whatever the input, a view within the limits stays within them. -/
theorem step_within {c : ViewConfig α} (hc : c.Valid) {v : View α} (hv : Within c v)
    (i : Input α) : Within c (step c v i) := by
  have hx : c.x.minSpan ≤ c.x.maxSpan := hc.1.2.2.1
  have hy : c.y.minSpan ≤ c.y.maxSpan := hc.2.2.2.1
  have zx := Interval.zoomAt_within hx hv.1
  have zy := Interval.zoomAt_within hy hv.2
  cases i with
  | wheel px py f => exact ⟨zx _ _, zy _ _⟩
  | pinch px py fx fy => exact ⟨zx _ _, zy _ _⟩
  | drag dx dy => exact ⟨Interval.drag_within hv.1 _, Interval.drag_within hv.2 _⟩
  | key k =>
    cases k
    · exact ⟨zx _ _, zy _ _⟩
    · exact ⟨zx _ _, zy _ _⟩
    · exact ⟨Interval.pan_within hv.1 _, hv.2⟩
    · exact ⟨Interval.pan_within hv.1 _, hv.2⟩
    · exact ⟨hv.1, Interval.pan_within hv.2 _⟩
    · exact ⟨hv.1, Interval.pan_within hv.2 _⟩
  | box x₀ y₀ x₁ y₁ => exact ⟨Interval.box_within hx _ _ _, Interval.box_within hy _ _ _⟩
  | set xs xe ys ye => exact ⟨Interval.fit_within hx _ _, Interval.fit_within hy _ _⟩
  | reset => exact home_within hc

/-- PROOF-9: the zoom limits hold in every reachable state. -/
theorem reachable_within {c : ViewConfig α} (hc : c.Valid) {v : View α} (h : Reachable c v) :
    Within c v := by
  induction h with
  | home => exact home_within hc
  | step i _ ih => exact step_within hc ih i

/-- PROOF-9: a wheel zoom keeps the data under the cursor fixed. -/
theorem cursor_wheel (c : ViewConfig α) (v : View α) (px py f : α) :
    cursor c (step c v (.wheel px py f)) px py = cursor c v px py := by
  simp only [step, cursor, Interval.toData_zoomAt]

/-- PROOF-9: a pinch keeps the data under its centre fixed. -/
theorem cursor_pinch (c : ViewConfig α) (v : View α) (px py fx fy : α) :
    cursor c (step c v (.pinch px py fx fy)) px py = cursor c v px py := by
  simp only [step, cursor, Interval.toData_zoomAt]

/-- PROOF-9: zooming in by a factor and out by the same factor about the same point restores the
view, unless a limit intervenes on the way in. -/
theorem wheel_wheel_inv {c : ViewConfig α} {v : View α} (hv : Within c v) (px py f : α)
    (hx : 0 < f → Interval.Within c.x ⟨v.x.start, v.x.span / f⟩)
    (hy : 0 < f → Interval.Within c.y ⟨v.y.start, v.y.span / f⟩) :
    step c (step c v (.wheel px py f)) (.wheel px py (1 / f)) = v := by
  cases v
  simp only [step]
  rw [Interval.zoomAt_zoomAt_inv px f hx hv.1, Interval.zoomAt_zoomAt_inv py f hy hv.2]

omit [DecidableLT α] in
/-- PROOF-10: the cursor's data position is mapped back to its screen position. -/
theorem toScreen_cursor {c : ViewConfig α} (hc : c.Valid) {v : View α} (hv : Within c v)
    (px py : α) :
    toScreen c v (cursor c v px py).1 (cursor c v px py).2 = (px, py) := by
  have sx : v.x.span ≠ 0 := by
    have := hc.1.2.1; have := hv.1.1; grind
  have sy : v.y.span ≠ 0 := by
    have := hc.2.2.1; have := hv.2.1; grind
  simp only [toScreen, cursor]
  rw [Interval.toScreen_toData _ _ sx (by have := hc.1.1; grind),
    Interval.toScreen_toData _ _ sy (by have := hc.2.1; grind)]

omit [DecidableLT α] in
/-- PROOF-10: a data position's screen position is mapped back to it by the cursor. -/
theorem cursor_toScreen {c : ViewConfig α} (hc : c.Valid) {v : View α} (hv : Within c v)
    (dx dy : α) :
    cursor c v (toScreen c v dx dy).1 (toScreen c v dx dy).2 = (dx, dy) := by
  have sx : v.x.span ≠ 0 := by
    have := hc.1.2.1; have := hv.1.1; grind
  have sy : v.y.span ≠ 0 := by
    have := hc.2.2.1; have := hv.2.1; grind
  simp only [toScreen, cursor]
  rw [Interval.toData_toScreen _ _ sx (by have := hc.1.1; grind),
    Interval.toData_toScreen _ _ sy (by have := hc.2.1; grind)]

section Step

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- A wheel notch zooms both axes by the same factor about the cursor. -/
theorem step_wheel (c : ViewConfig α) (v : View α) (px py f : α) :
    step c v (.wheel px py f) = ⟨v.x.zoomAt c.x px f, v.y.zoomAt c.y py f⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- A pinch zooms each axis by its own factor about the cursor. -/
theorem step_pinch (c : ViewConfig α) (v : View α) (px py fx fy : α) :
    step c v (.pinch px py fx fy) = ⟨v.x.zoomAt c.x px fx, v.y.zoomAt c.y py fy⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- A drag moves each axis by the screen distance. -/
theorem step_drag (c : ViewConfig α) (v : View α) (dx dy : α) :
    step c v (.drag dx dy) = ⟨v.x.drag c.x dx, v.y.drag c.y dy⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- Zoom in by key zooms about the centre of each axis by the configured factor. -/
theorem step_key_zoomIn (c : ViewConfig α) (v : View α) :
    step c v (.key .zoomIn) =
      ⟨v.x.zoomAt c.x (c.x.length / (1 + 1)) c.x.keyZoom, v.y.zoomAt c.y (c.y.length / (1 + 1)) c.y.keyZoom⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- Zoom out by key zooms about the centre of each axis by the reciprocal factor. -/
theorem step_key_zoomOut (c : ViewConfig α) (v : View α) :
    step c v (.key .zoomOut) =
      ⟨v.x.zoomAt c.x (c.x.length / (1 + 1)) (1 / c.x.keyZoom),
       v.y.zoomAt c.y (c.y.length / (1 + 1)) (1 / c.y.keyZoom)⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- Left pans x by a fraction of the span and leaves y. -/
theorem step_key_left (c : ViewConfig α) (v : View α) :
    step c v (.key .left) = ⟨v.x.pan (-(c.x.keyPan * v.x.span)), v.y⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- Right pans x by a fraction of the span and leaves y. -/
theorem step_key_right (c : ViewConfig α) (v : View α) :
    step c v (.key .right) = ⟨v.x.pan (c.x.keyPan * v.x.span), v.y⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- Up pans y by a fraction of the span and leaves x. -/
theorem step_key_up (c : ViewConfig α) (v : View α) :
    step c v (.key .up) = ⟨v.x, v.y.pan (-(c.y.keyPan * v.y.span))⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- Down pans y by a fraction of the span and leaves x. -/
theorem step_key_down (c : ViewConfig α) (v : View α) :
    step c v (.key .down) = ⟨v.x, v.y.pan (c.y.keyPan * v.y.span)⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- A box zooms each axis to the data under its corners. -/
theorem step_box (c : ViewConfig α) (v : View α) (x₀ y₀ x₁ y₁ : α) :
    step c v (.box x₀ y₀ x₁ y₁) = ⟨v.x.box c.x x₀ x₁, v.y.box c.y y₀ y₁⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- Setting fits each axis to the given data interval. -/
theorem step_set (c : ViewConfig α) (v : View α) (xs xe ys ye : α) :
    step c v (.set xs xe ys ye) = ⟨Interval.fit c.x xs xe, Interval.fit c.y ys ye⟩ := rfl

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- Reset returns the home view whatever the current one. -/
theorem step_reset (c : ViewConfig α) (v : View α) :
    step c v .reset = home c := rfl

end Step

end View

end Inkproof.Viewport

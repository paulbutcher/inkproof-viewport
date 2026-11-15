/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.Interval
import Inkproof.Scale.Proofs

universe u

namespace Inkproof.Viewport.Interval

open Lean.Grind

variable {α : Type u} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α]
  [OrderedRing α]

/-- The data value at a screen position is the start plus its fraction of the span. -/
theorem toData_eq (c : Config α) (a : Interval α) (p : α) :
    toData c a p = a.start + p * a.span / c.length := by
  simp only [toData, toLinear, Scale.Linear.inv, Scale.Linear.map]; grind

/-- The screen position of a data value is its fraction of the span along the screen length. -/
theorem toScreen_eq (c : Config α) (a : Interval α) (d : α) :
    toScreen c a d = (d - a.start) * c.length / a.span := by
  simp only [toScreen, toLinear, Scale.Linear.map]; grind

/-- PROOF-10: the data under the cursor is mapped back to the cursor's screen position. -/
theorem toScreen_toData (c : Config α) (a : Interval α) (hs : a.span ≠ 0) (hl : c.length ≠ 0)
    (p : α) : toScreen c a (toData c a p) = p := by
  rw [toScreen_eq, toData_eq]; grind

/-- PROOF-10: the screen position of a data value is mapped back to that value. -/
theorem toData_toScreen (c : Config α) (a : Interval α) (hs : a.span ≠ 0) (hl : c.length ≠ 0)
    (d : α) : toData c a (toScreen c a d) = d := by
  rw [toScreen_eq, toData_eq]; grind

/-- PROOF-9: zoom about a point keeps the data under that point fixed, for every factor. -/
theorem toData_zoomAt [DecidableLT α] (c : Config α) (a : Interval α) (p f : α) :
    toData c (zoomAt c a p f) p = toData c a p := by
  unfold zoomAt
  split
  · rw [toData_eq]; grind
  · rfl

section Clamp

variable [DecidableLT α]

/-- The clamp lies within its bounds when they are in order. -/
theorem clamp_within {lo hi : α} (h : lo ≤ hi) (x : α) :
    lo ≤ Float.clamp lo hi x ∧ Float.clamp lo hi x ≤ hi := by
  unfold Float.clamp; grind

/-- The clamp leaves a value already within its bounds alone. -/
theorem clamp_of_within {lo hi x : α} (h : lo ≤ x ∧ x ≤ hi) : Float.clamp lo hi x = x := by
  unfold Float.clamp; grind

end Clamp

section Limits

variable [DecidableLT α]

/-- PROOF-9: zoom keeps the span within the limits, whatever the factor. -/
theorem zoomAt_within {c : Config α} (hc : c.minSpan ≤ c.maxSpan) {a : Interval α} (ha : Within c a)
    (p f : α) : Within c (zoomAt c a p f) := by
  unfold zoomAt
  split
  · exact clamp_within hc _
  · exact ha

/-- PROOF-9: zooming in by a factor and out by the same factor at the same point restores the view,
provided the zoomed-in span is within the limits, so that no limit intervenes. A factor that is not
positive changes nothing, so it restores trivially. -/
theorem zoomAt_zoomAt_inv {c : Config α} {a : Interval α} (p f : α)
    (hf : 0 < f → Within c ⟨a.start, a.span / f⟩) (ha : Within c a) :
    zoomAt c (zoomAt c a p f) p (1 / f) = a := by
  by_cases h : 0 < f
  · have hinv : 0 < 1 / f := by
      rw [Field.div_eq_mul_inv, Semiring.one_mul]; exact Field.IsOrdered.inv_pos_iff.mpr h
    have h1 := hf h
    have hs : clampSpan c (a.span / f) = a.span / f := clamp_of_within h1
    have hf0 : f ≠ 0 := by grind
    have h2 : clampSpan c (a.span / f / (1 / f)) = a.span := by
      have : a.span / f / (1 / f) = a.span := by grind
      rw [this]; exact clamp_of_within ha
    simp only [zoomAt, h, hinv, ite_true, hs, h2, toData_eq]
    cases a; simp only; grind
  · have : ¬ 0 < 1 / f := by
      rw [Field.div_eq_mul_inv, Semiring.one_mul]; exact fun h' => h (Field.IsOrdered.inv_pos_iff.mp h')
    simp [zoomAt, h, this]

omit [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] [DecidableLT α] in
/-- Panning moves the start and keeps the span, so the limits still hold. -/
theorem pan_within {c : Config α} {a : Interval α} (ha : Within c a) (d : α) : Within c (pan a d) :=
  ha

omit [DecidableLT α] in
/-- Panning by a distance and back restores the view. -/
theorem pan_pan_neg (a : Interval α) (d : α) : pan (pan a d) (-d) = a := by
  cases a; simp only [pan]; grind

omit [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] [DecidableLT α] in
/-- Dragging keeps the span. -/
theorem drag_within {c : Config α} {a : Interval α} (ha : Within c a) (dp : α) :
    Within c (drag c a dp) := ha

/-- Fitting an interval gives a span within the limits. -/
theorem fit_within {c : Config α} (hc : c.minSpan ≤ c.maxSpan) (d₀ d₁ : α) :
    Within c (fit c d₀ d₁) := clamp_within hc _

/-- Box zoom gives a span within the limits. -/
theorem box_within {c : Config α} (hc : c.minSpan ≤ c.maxSpan) (a : Interval α) (p₀ p₁ : α) :
    Within c (box c a p₀ p₁) := fit_within hc _ _

end Limits

section Results

variable [DecidableLT α]

omit [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] [DecidableLT α] in
/-- Panning adds the distance to the start and keeps the span. -/
theorem pan_eq (a : Interval α) (d : α) : pan a d = ⟨a.start + d, a.span⟩ := rfl

omit [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] [DecidableLT α] in
/-- Dragging by `dp` screen units moves the start by minus `dp` scaled to data units. -/
theorem drag_eq (c : Config α) (a : Interval α) (dp : α) :
    drag c a dp = ⟨a.start - dp * a.span / c.length, a.span⟩ := by
  cases a; simp only [drag, pan]; congr 1; grind

/-- Fitting an interval whose span is within the limits shows exactly that interval. -/
theorem fit_of_le {c : Config α} {d₀ d₁ : α} (h : d₀ ≤ d₁) (hw : Within c ⟨d₀, d₁ - d₀⟩) :
    fit c d₀ d₁ = ⟨d₀, d₁ - d₀⟩ := by
  have hs : clampSpan c (d₁ - d₀) = d₁ - d₀ := clamp_of_within hw
  by_cases hlt : d₁ < d₀
  · exfalso; grind
  · simp only [fit, hlt, ite_false, hs]; congr 1; grind

omit [LE α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- Box zoom fits the data under its two corners. -/
theorem box_eq (c : Config α) (a : Interval α) (p₀ p₁ : α) :
    box c a p₀ p₁ = fit c (toData c a p₀) (toData c a p₁) := rfl

end Results

end Inkproof.Viewport.Interval

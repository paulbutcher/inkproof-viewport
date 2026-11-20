/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.Selection
import Inkproof.Viewport.Proofs.Interval

universe u

set_option linter.unusedSectionVars false

namespace Inkproof.Viewport.Selection

open Lean.Grind

section Plain

variable {α : Type u} [Add α] [Sub α] [LT α] [DecidableLT α]

theorem hit_none (c : Config α) (p : α) : hit c none p = .outside := rfl

theorem hit_lo (c : Config α) (b : Band α) (p : α) (h : near c.tolerance b.lo p = true)
    (hm : ¬(b.lo + b.hi < p + p)) : hit c (some b) p = .lo := by
  simp [hit, h, hm]

theorem hit_hi (c : Config α) (b : Band α) (p : α) (h : near c.tolerance b.hi p = true)
    (hm : b.lo + b.hi < p + p) : hit c (some b) p = .hi := by
  simp [hit, h, hm]

theorem press_eq (c : Config α) (sel : Option (Band α)) (p : α) :
    press c sel p = ⟨hit c sel p, p, sel⟩ := rfl

/-- A drag from outside draws the band between where it began and where it is. -/
theorem at_outside (c : Config α) (s : α) (sel : Option (Band α)) (p : α) :
    Drag.at c ⟨.outside, s, sel⟩ p = draw c s p := by
  simp [Drag.at]

/-- A drag from inside moves the band by how far the drag has gone, keeping its width. -/
theorem at_body (c : Config α) (s : α) (b : Band α) (p : α) :
    Drag.at c ⟨.body, s, some b⟩ p = some (shift c b (p - s)) := rfl

/-- A drag from the low edge moves that edge, the other staying fixed. -/
theorem at_lo (c : Config α) (s : α) (b : Band α) (p : α) :
    Drag.at c ⟨.lo, s, some b⟩ p = keep c (some b) (between c b.hi p) := rfl

/-- A drag from the high edge moves that edge, the other staying fixed. -/
theorem at_hi (c : Config α) (s : α) (b : Band α) (p : α) :
    Drag.at c ⟨.hi, s, some b⟩ p = keep c (some b) (between c b.lo p) := rfl

theorem near_iff (t e p : α) : near t e p = true ↔ ¬(p < e - t) ∧ ¬(e + t < p) := by
  simp [near]

theorem between_eq (c : Config α) (a b : α) :
    between c a b =
      ⟨Float.clamp c.domain.start (c.domain.start + c.domain.span) (if b < a then b else a),
       Float.clamp c.domain.start (c.domain.start + c.domain.span) (if b < a then a else b)⟩ := rfl

theorem keep_of_not_lt (c : Config α) (fallback : Option (Band α)) (b : Band α)
    (h : ¬(b.hi - b.lo < c.minWidth)) : keep c fallback b = some b := by
  simp [keep, h]

theorem keep_of_lt (c : Config α) (fallback : Option (Band α)) (b : Band α)
    (h : b.hi - b.lo < c.minWidth) : keep c fallback b = fallback := by
  simp [keep, h]

theorem draw_of_not_lt (c : Config α) (a b : α) (h : ¬((between c a b).hi - (between c a b).lo < c.minWidth)) :
    draw c a b = some (between c a b) := keep_of_not_lt c none _ h

theorem draw_of_lt (c : Config α) (a b : α) (h : (between c a b).hi - (between c a b).lo < c.minWidth) :
    draw c a b = none := keep_of_lt c none _ h

theorem shift_lo (c : Config α) (b : Band α) (d : α) :
    (shift c b d).lo =
      Float.clamp c.domain.start (c.domain.start + c.domain.span - (b.hi - b.lo)) (b.lo + d) := rfl

theorem toInterval_start (b : Band α) : b.toInterval.start = b.lo := rfl

theorem toInterval_span (b : Band α) : b.toInterval.span = b.hi - b.lo := rfl

theorem ofInterval_eq (c : Config α) (a : Interval α) :
    ofInterval c a = draw c a.start (a.start + a.span) := rfl

end Plain

variable {α : Type u} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α]
  [OrderedRing α] [DecidableLT α]

theorem hit_body (c : Config α) (b : Band α) (p : α) (ht : 0 ≤ c.tolerance)
    (h₁ : b.lo + c.tolerance < p) (h₂ : p < b.hi - c.tolerance) : hit c (some b) p = .body := by
  have n₁ : near c.tolerance b.lo p = false := by simp [near]; grind
  have n₂ : near c.tolerance b.hi p = false := by simp [near]; grind
  simp [hit, n₁, n₂]; grind

theorem hit_outside (c : Config α) (b : Band α) (p : α) (ht : 0 ≤ c.tolerance)
    (hb : b.lo ≤ b.hi) (h : p < b.lo - c.tolerance ∨ b.hi + c.tolerance < p) : hit c (some b) p = .outside := by
  have n₁ : near c.tolerance b.lo p = false := by simp [near]; grind
  have n₂ : near c.tolerance b.hi p = false := by simp [near]; grind
  simp [hit, n₁, n₂]; grind

theorem shift_width (c : Config α) (b : Band α) (d : α) :
    (shift c b d).hi - (shift c b d).lo = b.hi - b.lo := by
  simp only [shift]; grind

theorem between_within (c : Config α) (h : 0 ≤ c.domain.span) (a b : α) :
    (between c a b).Within c := by
  unfold between Band.Within
  have h₁ := Interval.clamp_within (lo := c.domain.start) (hi := c.domain.start + c.domain.span)
    (by grind) (if b < a then b else a)
  have h₂ := Interval.clamp_within (lo := c.domain.start) (hi := c.domain.start + c.domain.span)
    (by grind) (if b < a then a else b)
  have key : (if b < a then b else a) ≤ (if b < a then a else b) := by split <;> grind
  have mono : ∀ x y : α, x ≤ y →
      Float.clamp c.domain.start (c.domain.start + c.domain.span) x ≤
        Float.clamp c.domain.start (c.domain.start + c.domain.span) y := by
    intro x y hxy; unfold Float.clamp; grind
  exact ⟨h₁.1, mono _ _ key, h₂.2⟩

theorem shift_within (c : Config α) (b : Band α) (hb : b.Within c) (d : α) :
    (shift c b d).Within c := by
  unfold shift Band.Within at *
  have := Interval.clamp_within (lo := c.domain.start)
    (hi := c.domain.start + c.domain.span - (b.hi - b.lo)) (by grind) (b.lo + d)
  grind

theorem keep_within (c : Config α) (fallback : Option (Band α)) (b : Band α)
    (hf : ∀ f, fallback = some f → f.Within c) (hb : b.Within c) :
    ∀ r, keep c fallback b = some r → r.Within c := by
  intro r h
  unfold keep at h
  split at h
  · exact hf r h
  · cases h; exact hb

/-- A selection stays within the domain and ordered through every drag, given one that was. -/
theorem at_within (c : Config α) (h : 0 ≤ c.domain.span) (d : Drag α)
    (hd : ∀ b, d.before = some b → b.Within c) (p : α) :
    ∀ r, d.at c p = some r → r.Within c := by
  intro r hr
  obtain ⟨g, s, bf⟩ := d
  simp only at hd
  unfold Drag.at at hr
  simp only at hr
  split at hr
  · cases hr; exact shift_within c _ (hd _ rfl) _
  · exact keep_within c _ _ (fun f hf => hd f hf) (between_within c h _ _) r hr
  · exact keep_within c _ _ (fun f hf => hd f hf) (between_within c h _ _) r hr
  · exact keep_within c _ _ (by simp) (between_within c h _ _) r hr

/-- Pressing and then dragging keeps a selection within the domain. -/
theorem press_at_within (c : Config α) (h : 0 ≤ c.domain.span) (sel : Option (Band α))
    (hs : ∀ b, sel = some b → b.Within c) (s p : α) :
    ∀ r, (press c sel s).at c p = some r → r.Within c :=
  at_within c h _ hs p

theorem ofInterval_within (c : Config α) (h : 0 ≤ c.domain.span) (a : Interval α) :
    ∀ r, ofInterval c a = some r → r.Within c :=
  keep_within c none _ (by simp) (between_within c h _ _)

/-- A band within the domain and wide enough is recovered from its view range. -/
theorem ofInterval_toInterval (c : Config α) (b : Band α) (hb : b.Within c)
    (hw : ¬(b.hi - b.lo < c.minWidth)) : ofInterval c b.toInterval = some b := by
  obtain ⟨b₁, b₂, b₃⟩ := hb
  have e : b.lo + (b.hi - b.lo) = b.hi := by grind
  have c₁ : Float.clamp c.domain.start (c.domain.start + c.domain.span) b.lo = b.lo :=
    Interval.clamp_of_within (by grind)
  have c₂ : Float.clamp c.domain.start (c.domain.start + c.domain.span) b.hi = b.hi :=
    Interval.clamp_of_within (by grind)
  have n : ¬(b.hi < b.lo) := by grind
  unfold ofInterval draw keep between Band.toInterval
  simp only [e, c₁, c₂, n, ite_false, hw]

end Selection

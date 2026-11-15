/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.Event

universe u

namespace Inkproof.Viewport.View

variable {α : Type u}

/-- Applying a received change gives the view it carries. -/
theorem receive_eq (v : View α) (e : ViewChange α) : receive v e = e.view := rfl

/-- VIEW-4: applying a received change is idempotent. -/
theorem receive_receive (v : View α) (e : ViewChange α) :
    receive (receive v e) e = receive v e := rfl

section Emit

variable [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
  [BEq α] [LawfulBEq α]

omit [LawfulBEq α] in
/-- VIEW-4: the view is the one `step` gives. -/
theorem stepEvent_fst (c : ViewConfig α) (v : View α) (i : Input α) :
    (stepEvent c v i).1 = step c v i := rfl

omit [LawfulBEq α] in
/-- VIEW-4: when a step changes the view, the event it yields, applied to the prior view, gives the
new view. -/
theorem receive_of_stepEvent {c : ViewConfig α} {v : View α} {i : Input α} {e : ViewChange α}
    (h : (stepEvent c v i).2 = some e) : receive v e = (stepEvent c v i).1 := by
  simp only [stepEvent] at h ⊢
  split at h
  · simp at h
  · simp at h; subst h; rfl

/-- VIEW-4: a step that yields no event leaves the view unchanged. -/
theorem eq_of_stepEvent_none {c : ViewConfig α} {v : View α} {i : Input α}
    (h : (stepEvent c v i).2 = none) : (stepEvent c v i).1 = v := by
  simp only [stepEvent] at h ⊢
  split at h
  · exact eq_of_beq ‹_›
  · simp at h

/-- VIEW-4: a step yields an event exactly when it changes the view. -/
theorem stepEvent_isSome {c : ViewConfig α} {v : View α} {i : Input α} :
    (stepEvent c v i).2.isSome = true ↔ step c v i ≠ v := by
  simp only [stepEvent]
  split <;> simp_all

end Emit

end Inkproof.Viewport.View

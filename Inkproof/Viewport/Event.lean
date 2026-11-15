/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.View

universe u

namespace Inkproof.Viewport

/-- A change of view, carrying the new visible ranges, which is enough to reproduce it. -/
structure ViewChange (α : Type u) where
  view : View α
  deriving Repr, BEq

namespace View

variable {α : Type u}

/-- Apply a change received from elsewhere. It produces a view and no event, so applying one never
echoes. -/
def receive (_ : View α) (e : ViewChange α) : View α := e.view

section Emit

variable [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
  [BEq α]

/-- The view after an input, and the event for the host to forward if the view changed. -/
def stepEvent (c : ViewConfig α) (v : View α) (i : Input α) : View α × Option (ViewChange α) :=
  let v' := step c v i
  (v', if v' == v then none else some ⟨v'⟩)

end Emit

end View

end Inkproof.Viewport

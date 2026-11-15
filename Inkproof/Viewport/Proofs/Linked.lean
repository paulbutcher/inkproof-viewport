/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.Linked
import Inkproof.Viewport.Proofs.View

universe u

namespace Inkproof.Viewport.Linked

variable {α : Type u} {n : Nat}

/-- PROOF-10: linked views draw with the identical x transform in every state. -/
theorem xTransform_eq [Add α] [OfNat α 0] (c : ViewConfig α) (g : Linked α n) (i j : Fin n) :
    xTransform c g i = xTransform c g j := rfl

/-- Every linked view shows the shared x axis. -/
theorem view_x (g : Linked α n) (i : Fin n) : (g.view i).x = g.x.scale := rfl

section Step

variable [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
  (c : ViewConfig α) (g : Linked α n) (i : Fin n) (inp : Input α)

/-- VIEW-3: after an input to one view, every view shows the x axis that view arrived at. -/
theorem view_x_step (j : Fin n) :
    ((g.step c i inp).view j).x = (View.step c (g.view i) inp).x := rfl

/-- The view the input went to shows exactly what the single-view step gives. -/
theorem view_step_self : (g.step c i inp).view i = View.step c (g.view i) inp := by
  simp [step, view]; rfl

/-- An input to one view leaves the y axis of every other view alone. -/
theorem view_y_step_of_ne {j : Fin n} (h : j ≠ i) : ((g.step c i inp).view j).y = (g.view j).y := by
  simp [step, view, h]

end Step

end Inkproof.Viewport.Linked

/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.View

universe u

namespace Inkproof.Viewport

/-- `n` views that share one x axis, each with its own y axis. The shared axis is held once, so
a change through any view is seen by all. -/
structure Linked (α : Type u) (n : Nat) where
  x : Scale.Shared (Interval α)
  y : Fin n → Interval α

namespace Linked

variable {α : Type u} {n : Nat}

/-- What view `i` shows. -/
def view (g : Linked α n) (i : Fin n) : View α := ⟨g.x.scale, g.y i⟩

/-- The x transform view `i` draws with. -/
def xTransform [Add α] [OfNat α 0] (c : ViewConfig α) (g : Linked α n) (i : Fin n) :
    Scale.Linear α :=
  (g.view i).x.toLinear c.x

/-- Apply an input to view `i`: its x change goes to the shared axis, its y change stays with it. -/
def step [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
    (c : ViewConfig α) (g : Linked α n) (i : Fin n) (inp : Input α) : Linked α n :=
  let v := View.step c (g.view i) inp
  ⟨g.x.update fun _ => v.x, fun j => if j = i then v.y else g.y j⟩

end Linked

end Inkproof.Viewport

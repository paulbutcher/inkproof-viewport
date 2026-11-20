/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.View

universe u

namespace Inkproof.Viewport

/-- `n` views that share one x axis, each with its own y axis. The shared axis is held once, so
a change through any view is seen by all. A view can be unlinked: it then keeps its own x axis, and
inputs to it leave the shared axis alone. -/
structure Linked (α : Type u) (n : Nat) where
  x : Scale.Shared (Interval α)
  y : Fin n → Interval α
  own : Fin n → Option (Interval α) := fun _ => none

namespace Linked

variable {α : Type u} {n : Nat}

/-- What view `i` shows. -/
def view (g : Linked α n) (i : Fin n) : View α := ⟨(g.own i).getD g.x.scale, g.y i⟩

/-- Whether view `i` follows the shared x axis. -/
def isLinked (g : Linked α n) (i : Fin n) : Bool := (g.own i).isNone

/-- Detach view `i` from the shared x axis, keeping the x it shows now. -/
def unlink (g : Linked α n) (i : Fin n) : Linked α n :=
  { g with own := fun j => if j = i then some (g.view i).x else g.own j }

/-- Reattach view `i` to the shared x axis, which it then shows. -/
def relink (g : Linked α n) (i : Fin n) : Linked α n :=
  { g with own := fun j => if j = i then none else g.own j }

/-- The x transform view `i` draws with. -/
def xTransform [Add α] [OfNat α 0] (c : ViewConfig α) (g : Linked α n) (i : Fin n) :
    Scale.Linear α :=
  (g.view i).x.toLinear c.x

/-- Apply an input to view `i`: its y change stays with it, and its x change goes to the shared axis,
or to its own axis if it is unlinked. -/
def step [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
    (c : ViewConfig α) (g : Linked α n) (i : Fin n) (inp : Input α) : Linked α n :=
  let v := View.step c (g.view i) inp
  { x := if g.isLinked i then g.x.update fun _ => v.x else g.x
    y := fun j => if j = i then v.y else g.y j
    own := fun j => if j = i && !g.isLinked i then some v.x else g.own j }

/-- Apply an input to view `i` of a group whose size is known only at run time, every view of which
follows the shared x axis: all views take the x range the view reached, and only view `i` takes its
y range. An index out of range leaves the group unchanged. -/
def stepArray [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
    (c : ViewConfig α) (vs : Array (View α)) (i : Nat) (inp : Input α) : Array (View α) :=
  match vs[i]? with
  | none => vs
  | some v =>
    let v' := View.step c v inp
    vs.mapIdx fun j w => if j = i then v' else { w with x := v'.x }

end Linked

end Inkproof.Viewport

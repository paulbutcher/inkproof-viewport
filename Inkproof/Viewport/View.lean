/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.Interval

universe u

namespace Inkproof.Viewport

/-- The visible ranges of a two-axis view. -/
structure View (α : Type u) where
  x : Interval α
  y : Interval α
  deriving Repr, BEq, ReflBEq, LawfulBEq

/-- The configuration of each axis. -/
structure ViewConfig (α : Type u) where
  x : Interval.Config α
  y : Interval.Config α
  deriving Repr

/-- Both axes satisfy their configuration's validity. -/
def ViewConfig.Valid {α : Type u} [OfNat α 0] [LE α] [LT α] (c : ViewConfig α) : Prop :=
  c.x.Valid ∧ c.y.Valid

/-- Both axes are within their zoom limits. -/
def View.Within {α : Type u} [LE α] (c : ViewConfig α) (v : View α) : Prop :=
  v.x.Within c.x ∧ v.y.Within c.y

inductive Key where
  | zoomIn | zoomOut | left | right | up | down
  deriving Repr, DecidableEq

/-- What a host can tell a view. Positions and drags are in screen units, factors above one zoom
in, and `set` takes data intervals. A wheel notch or pinch is already converted to a factor by the
host, which keeps the view independent of timing and platform. -/
inductive Input (α : Type u) where
  | wheel (x y factor : α)
  | pinch (x y xFactor yFactor : α)
  | drag (dx dy : α)
  | key (k : Key)
  | box (x₀ y₀ x₁ y₁ : α)
  | set (xStart xEnd yStart yEnd : α)
  | reset
  deriving Repr

namespace View

variable {α : Type u}

section Step

variable [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]

/-- The view after one input. Total: every input, however odd, gives a view. -/
def step (c : ViewConfig α) (v : View α) : Input α → View α
  | .wheel px py f => ⟨v.x.zoomAt c.x px f, v.y.zoomAt c.y py f⟩
  | .pinch px py fx fy => ⟨v.x.zoomAt c.x px fx, v.y.zoomAt c.y py fy⟩
  | .drag dx dy => ⟨v.x.drag c.x dx, v.y.drag c.y dy⟩
  | .key .zoomIn =>
    ⟨v.x.zoomAt c.x (c.x.length / (1 + 1)) c.x.keyZoom,
     v.y.zoomAt c.y (c.y.length / (1 + 1)) c.y.keyZoom⟩
  | .key .zoomOut =>
    ⟨v.x.zoomAt c.x (c.x.length / (1 + 1)) (1 / c.x.keyZoom),
     v.y.zoomAt c.y (c.y.length / (1 + 1)) (1 / c.y.keyZoom)⟩
  | .key .left => ⟨v.x.pan (-(c.x.keyPan * v.x.span)), v.y⟩
  | .key .right => ⟨v.x.pan (c.x.keyPan * v.x.span), v.y⟩
  | .key .up => ⟨v.x, v.y.pan (-(c.y.keyPan * v.y.span))⟩
  | .key .down => ⟨v.x, v.y.pan (c.y.keyPan * v.y.span)⟩
  | .box x₀ y₀ x₁ y₁ => ⟨v.x.box c.x x₀ x₁, v.y.box c.y y₀ y₁⟩
  | .set xs xe ys ye => ⟨Interval.fit c.x xs xe, Interval.fit c.y ys ye⟩
  | .reset => ⟨c.x.home, c.y.home⟩

/-- The data coordinates under a screen position, for a cursor. -/
def cursor (c : ViewConfig α) (v : View α) (px py : α) : α × α :=
  (v.x.toData c.x px, v.y.toData c.y py)

/-- The screen position of a point in data coordinates. -/
def toScreen (c : ViewConfig α) (v : View α) (dx dy : α) : α × α :=
  (v.x.toScreen c.x dx, v.y.toScreen c.y dy)

end Step

/-- The view a configuration starts in. -/
def home (c : ViewConfig α) : View α := ⟨c.x.home, c.y.home⟩

/-- Every view reachable from `home` by inputs. -/
inductive Reachable (c : ViewConfig α) [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0]
    [OfNat α 1] [LT α] [DecidableLT α] : View α → Prop where
  | home : Reachable c (home c)
  | step {v : View α} (i : Input α) : Reachable c v → Reachable c (step c v i)

end View

end Inkproof.Viewport

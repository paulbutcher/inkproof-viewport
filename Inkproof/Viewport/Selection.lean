/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport.Interval

universe u

namespace Inkproof.Viewport

namespace Selection

/-- A selected range of data, from `lo` to `hi`. -/
structure Band (α : Type u) where
  lo : α
  hi : α
  deriving Repr, BEq, ReflBEq, LawfulBEq

/-- What a selection lives in: the `domain` it is clamped to, the narrowest band worth keeping, and
how far from an edge a position still grabs it, both in data units. -/
structure Config (α : Type u) where
  domain : Interval α
  minWidth : α
  tolerance : α
  deriving Repr

/-- What a position would grab. -/
inductive Grab where
  | outside | body | lo | hi
  deriving Repr, BEq, DecidableEq

/-- A drag in progress: what it grabbed, where it began and the selection it began with. -/
structure Drag (α : Type u) where
  grab : Grab
  start : α
  before : Option (Band α)

variable {α : Type u}

/-- The band lies within the domain and is ordered. -/
def Band.Within [LE α] [Add α] (c : Config α) (b : Band α) : Prop :=
  c.domain.start ≤ b.lo ∧ b.lo ≤ b.hi ∧ b.hi ≤ c.domain.start + c.domain.span

/-- The band's data range as a view's range, for a view to show it. -/
def Band.toInterval [Sub α] (b : Band α) : Interval α := ⟨b.lo, b.hi - b.lo⟩

/-- Whether `p` is within `t` of `e`. -/
def near [Add α] [Sub α] [LT α] [DecidableLT α] (t e p : α) : Bool :=
  !decide (p < e - t) && !decide (e + t < p)

/-- What a position grabs: an edge within the tolerance, else the body, else nothing. Where the
tolerances of both edges overlap, the nearer half of the band decides. -/
def hit [Add α] [Sub α] [LT α] [DecidableLT α] (c : Config α) (sel : Option (Band α)) (p : α) : Grab :=
  match sel with
  | none => .outside
  | some b =>
    if near c.tolerance b.lo p && !decide (b.lo + b.hi < p + p) then .lo
    else if near c.tolerance b.hi p then .hi
    else if !decide (p < b.lo) && !decide (b.hi < p) then .body
    else .outside

/-- The start of a drag at `p` over the selection `sel`. -/
def press [Add α] [Sub α] [LT α] [DecidableLT α] (c : Config α) (sel : Option (Band α)) (p : α) :
    Drag α :=
  ⟨hit c sel p, p, sel⟩

/-- The ordered band between two positions, held to the domain. -/
def between [Add α] [LT α] [DecidableLT α] (c : Config α) (a b : α) : Band α :=
  let hi := c.domain.start + c.domain.span
  ⟨Float.clamp c.domain.start hi (if b < a then b else a),
   Float.clamp c.domain.start hi (if b < a then a else b)⟩

/-- `b` unless it is narrower than the minimum, when `fallback`. -/
def keep [Sub α] [LT α] [DecidableLT α] (c : Config α) (fallback : Option (Band α)) (b : Band α) :
    Option (Band α) :=
  if b.hi - b.lo < c.minWidth then fallback else some b

/-- The band drawn between two positions, or none if it is too narrow. -/
def draw [Add α] [Sub α] [LT α] [DecidableLT α] (c : Config α) (a b : α) : Option (Band α) :=
  keep c none (between c a b)

/-- `b` moved by `d`, held to the domain without changing its width. -/
def shift [Add α] [Sub α] [LT α] [DecidableLT α] (c : Config α) (b : Band α) (d : α) : Band α :=
  let lo := Float.clamp c.domain.start (c.domain.start + c.domain.span - (b.hi - b.lo)) (b.lo + d)
  ⟨lo, lo + (b.hi - b.lo)⟩

/-- The selection after the drag reaches `p`. Dragging from outside draws a band, from the body
moves it, from an edge moves that edge, the band swapping ends if the edge passes the other. A
drawn band that is too narrow is cleared, a resized one is left as it was. -/
def Drag.at [Add α] [Sub α] [LT α] [DecidableLT α] (c : Config α) (d : Drag α) (p : α) :
    Option (Band α) :=
  match d.grab, d.before with
  | .body, some b => some (shift c b (p - d.start))
  | .lo, some b => keep c d.before (between c b.hi p)
  | .hi, some b => keep c d.before (between c b.lo p)
  | _, _ => draw c d.start p

/-- The band a view's range covers, held to the domain, if wide enough. -/
def ofInterval [Add α] [Sub α] [LT α] [DecidableLT α] (c : Config α) (a : Interval α) :
    Option (Band α) :=
  draw c a.start (a.start + a.span)

end Selection

end Inkproof.Viewport

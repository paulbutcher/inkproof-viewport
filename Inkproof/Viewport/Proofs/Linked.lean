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
theorem xTransform_eq [Add α] [OfNat α 0] (c : ViewConfig α) (g : Linked α n) {i j : Fin n}
    (hi : g.isLinked i = true) (hj : g.isLinked j = true) : xTransform c g i = xTransform c g j := by
  simp [isLinked, Option.isNone_iff_eq_none] at hi hj
  simp [xTransform, view, hi, hj]

/-- A linked view shows the shared x axis. -/
theorem view_x (g : Linked α n) {i : Fin n} (h : g.isLinked i = true) : (g.view i).x = g.x.scale := by
  simp [isLinked, Option.isNone_iff_eq_none] at h
  simp [view, h]

/-- Unlinking leaves what every view shows unchanged. -/
theorem view_unlink (g : Linked α n) (i j : Fin n) : (g.unlink i).view j = g.view j := by
  by_cases h : j = i <;> simp [unlink, view, h]

/-- Relinking a view makes it show the shared x axis. -/
theorem view_relink (g : Linked α n) (i : Fin n) : ((g.relink i).view i).x = g.x.scale := by
  simp [relink, view]

/-- Relinking leaves the other views alone. -/
theorem view_relink_of_ne (g : Linked α n) {i j : Fin n} (h : j ≠ i) :
    (g.relink i).view j = g.view j := by
  simp [relink, view, h]

theorem isLinked_iff (g : Linked α n) (i : Fin n) : g.isLinked i = true ↔ g.own i = none := by
  simp [isLinked, Option.isNone_iff_eq_none]

theorem isLinked_unlink (g : Linked α n) (i : Fin n) : (g.unlink i).isLinked i = false := by
  simp [unlink, isLinked]

theorem isLinked_relink (g : Linked α n) (i : Fin n) : (g.relink i).isLinked i = true := by
  simp [relink, isLinked]

section Step

variable [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
  (c : ViewConfig α) (g : Linked α n) (i : Fin n) (inp : Input α)

/-- After an input to a linked view, every linked view shows the x axis that view arrived at. -/
theorem view_x_step (hi : g.isLinked i = true) {j : Fin n} (hj : g.isLinked j = true) :
    ((g.step c i inp).view j).x = (View.step c (g.view i) inp).x := by
  simp [isLinked, Option.isNone_iff_eq_none] at hi hj
  simp [step, view, isLinked, hi, hj]
  rfl

/-- An input to an unlinked view leaves the shared axis alone. -/
theorem x_step_unlinked (hi : g.isLinked i = false) : (g.step c i inp).x = g.x := by
  simp [step, hi]

/-- The view the input went to shows exactly what the single-view step gives. -/
theorem view_step_self : (g.step c i inp).view i = View.step c (g.view i) inp := by
  unfold step view isLinked
  cases h : g.own i <;> simp [h] <;> rfl

/-- An input to one view leaves the y axis of every other view alone. -/
theorem view_y_step_of_ne {j : Fin n} (h : j ≠ i) : ((g.step c i inp).view j).y = (g.view j).y := by
  simp [step, view, h]

end Step

section StepArray

variable [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
  (c : ViewConfig α) (vs : Array (View α)) (i : Nat) (inp : Input α)

/-- A step keeps the number of views. -/
theorem size_stepArray : (stepArray c vs i inp).size = vs.size := by
  unfold stepArray
  split <;> simp

/-- With every view linked, the array step shows what `Linked.step` shows. -/
theorem stepArray_eq_step (g : Linked α n) (hg : ∀ j, g.isLinked j = true) (i : Fin n) :
    stepArray c (Array.ofFn g.view) i inp = Array.ofFn (g.step c i inp).view := by
  have hi : (Array.ofFn g.view)[(i : Nat)]? = some (g.view i) := by simp
  apply Array.ext
  · simp [size_stepArray]
  · intro j hj1 hj2
    have hj : j < n := by simpa [size_stepArray] using hj1
    simp only [stepArray, hi, Array.getElem_mapIdx, Array.getElem_ofFn]
    by_cases h : j = i
    · subst h
      simp [view_step_self]
    · have h' : (⟨j, hj⟩ : Fin n) ≠ i := fun e => h (by simpa using congrArg Fin.val e)
      have hx := view_x_step c g i inp (hg i) (j := ⟨j, hj⟩) (hg _)
      have hy := view_y_step_of_ne c g i inp h'
      simp only [h, ite_false]
      cases hv : (g.step c i inp).view ⟨j, hj⟩
      simp_all

end StepArray

end Inkproof.Viewport.Linked

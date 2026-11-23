/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/Arrow.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: the one-sorted type of arrows.

The paper suppresses associators and unitors, and for a strict monoidal
category it identifies, e.g., `(a ⊗ b) ⊗ c` with `a ⊗ (b ⊗ c)`.  In Lean these
objects are only propositionally equal, so two morphisms whose types differ by
`mul_assoc` cannot be compared with `=` directly.  Following design decision D2
of `formalization/PLAN.md`, such laws are stated in Mathlib's type
`Arrow C` of all arrows of `C` (the arrows of the paper's "underlying graph
monoid"), where `Arrow.mk f = Arrow.mk g` says that `f` and `g` agree after
identifying their sources and targets.  This file collects the small calculus
of such equations that the later files use.
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.EqToHom

@[expose] public section

universe v u

namespace CategoryTheory.Arrow

variable {T : Type u} [Category.{v} T]

theorem left_eq_of_mk_eq {X Y X' Y' : T} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : Arrow.mk f = Arrow.mk f') : X = X' :=
  congr($(h).left)

theorem right_eq_of_mk_eq {X Y X' Y' : T} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : Arrow.mk f = Arrow.mk f') : Y = Y' :=
  congr($(h).right)

/-- The form of an equation in `Arrow T` that is used for rewriting. -/
theorem comp_eqToHom_eq_of_mk_eq {X Y X' Y' : T} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : Arrow.mk f = Arrow.mk f') (hX : X = X') (hY : Y = Y') :
    f ≫ eqToHom hY = eqToHom hX ≫ f' := by
  obtain ⟨rfl, rfl, rfl⟩ := (mk_eq_mk_iff _ _).1 h
  simp

theorem mk_eq_of_comp_eqToHom_eq {X Y X' Y' : T} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (hX : X = X') (hY : Y = Y') (h : f ≫ eqToHom hY = eqToHom hX ≫ f') :
    Arrow.mk f = Arrow.mk f' := by
  subst hX hY
  simpa using congrArg Arrow.mk h

theorem eq_of_mk_eq {X Y : T} {f g : X ⟶ Y} (h : Arrow.mk f = Arrow.mk g) : f = g :=
  (mk_inj _ _).1 h

@[simp]
theorem mk_eqToHom {X Y : T} (h : X = Y) : Arrow.mk (eqToHom h) = Arrow.mk (𝟙 X) := by
  subst h
  rfl

theorem mk_id_congr {X Y : T} (h : X = Y) : Arrow.mk (𝟙 X) = Arrow.mk (𝟙 Y) := by
  subst h
  rfl

/-- Equality in `Arrow T` is a congruence for composition. -/
theorem mk_comp_congr {X Y Z X' Y' Z' : T} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'}
    {g' : Y' ⟶ Z'} (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨rfl, rfl, rfl⟩ := (mk_eq_mk_iff _ _).1 hf
  obtain ⟨-, rfl, rfl⟩ := (mk_eq_mk_iff _ _).1 hg
  simp

theorem mk_comp_eqToHom_comp {X Y Y' Z : T} (f : X ⟶ Y) (h : Y = Y') (g : Y' ⟶ Z) :
    Arrow.mk (f ≫ eqToHom h ≫ g) = Arrow.mk (f ≫ (eqToHom h ≫ g)) := rfl

end CategoryTheory.Arrow

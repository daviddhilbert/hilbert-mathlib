/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/Strict/Bridge.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: the bridge to Mathlib.

Every symmetric strict monoidal category (in the sense of `StrictSMC`) is a
Mathlib `MonoidalCategory` and `SymmetricCategory` whose associators and unitors
are `eqToIso`, and every strict Markov category is a Mathlib `MarkovCategory`
with `Δ[a] = δ_a` and `ε[a] = ε_a`.  The final theorems of the paper are restated
through this bridge, so that "Markov category" there means Mathlib's definition.
-/
module

public import HilbertMathlib.Foundation.CategoryTheory.Strict.Lemmas
public import Mathlib.CategoryTheory.MarkovCategory.Basic

@[expose] public section

universe v u

namespace FreeMarkov

open CategoryTheory MonoidalCategory StrictSMC

namespace StrictSMC

variable (C : Type u) [Monoid C] [Category.{v} C] [StrictSMC C]

/-- The monoidal data: `a ⊗ b = a * b`, `𝟙_ = 1`, whiskerings are tensor products
with identities, associators and unitors are `eqToIso`. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct C where
  tensorObj a b := a * b
  whiskerLeft a _ _ f := 𝟙 a ⊗ₛ f
  whiskerRight f b := f ⊗ₛ 𝟙 b
  tensorHom f g := f ⊗ₛ g
  tensorUnit := 1
  associator a b c := eqToIso (mul_assoc a b c)
  leftUnitor a := eqToIso (one_mul a)
  rightUnitor a := eqToIso (mul_one a)

variable {C}

@[simp] theorem tensorObj_eq (a b : C) : a ⊗ b = a * b := rfl
@[simp] theorem tensorUnit_eq : 𝟙_ C = 1 := rfl
@[simp] theorem tensorHom_eq {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) : f ⊗ₘ g = f ⊗ₛ g := rfl
@[simp] theorem whiskerLeft_eq (a : C) {b c : C} (f : b ⟶ c) : a ◁ f = 𝟙 a ⊗ₛ f := rfl
@[simp] theorem whiskerRight_eq {a b : C} (f : a ⟶ b) (c : C) : f ▷ c = f ⊗ₛ 𝟙 c := rfl
@[simp] theorem associator_eq (a b c : C) : α_ a b c = eqToIso (mul_assoc a b c) := rfl
@[simp] theorem leftUnitor_eq (a : C) : λ_ a = eqToIso (one_mul a) := rfl
@[simp] theorem rightUnitor_eq (a : C) : ρ_ a = eqToIso (mul_one a) := rfl

variable (C)

/-- **Bridge, monoidal part.** A symmetric strict monoidal category is a Mathlib
monoidal category. -/
instance monoidalCategory : MonoidalCategory C where
  tensorHom_def f g := by
    simp only [tensorHom_eq, whiskerRight_eq, whiskerLeft_eq, tensorHom_comp',
      Category.comp_id, Category.id_comp]
  id_tensorHom_id a b := tensorHom_id a b
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := tensorHom_comp' f₁ g₁ f₂ g₂
  whiskerLeft_id a b := tensorHom_id a b
  id_whiskerRight a b := tensorHom_id a b
  associator_naturality f₁ f₂ f₃ := by
    simp only [tensorHom_eq, associator_eq, eqToIso.hom]
    exact Arrow.comp_eqToHom_eq_of_mk_eq (tensorHom_assoc f₁ f₂ f₃) _ _
  leftUnitor_naturality f := by
    simp only [whiskerLeft_eq, tensorUnit_eq, leftUnitor_eq, eqToIso.hom]
    exact Arrow.comp_eqToHom_eq_of_mk_eq (id_one_tensorHom f) _ _
  rightUnitor_naturality f := by
    simp only [whiskerRight_eq, tensorUnit_eq, rightUnitor_eq, eqToIso.hom]
    exact Arrow.comp_eqToHom_eq_of_mk_eq (tensorHom_id_one f) _ _
  pentagon a b c d := by
    simp only [whiskerRight_eq, whiskerLeft_eq, associator_eq, eqToIso.hom,
      eqToHom_tensorHom_id, id_tensorHom_eqToHom, eqToHom_trans]
  triangle a b := by
    simp only [whiskerRight_eq, whiskerLeft_eq, associator_eq, leftUnitor_eq,
      rightUnitor_eq, tensorUnit_eq, eqToIso.hom, eqToHom_tensorHom_id,
      id_tensorHom_eqToHom, eqToHom_trans]

/-- The braiding `σ_{a,b}` as an isomorphism, with inverse `σ_{b,a}`. -/
def braidIso (a b : C) : a * b ≅ b * a where
  hom := σ_ a b
  inv := σ_ b a
  hom_inv_id := braid_braid a b
  inv_hom_id := braid_braid b a

/-- **Bridge, symmetric part.** A symmetric strict monoidal category is a Mathlib
symmetric monoidal category, with braiding `σ`. -/
instance symmetricCategory : SymmetricCategory C where
  braiding a b := braidIso C a b
  braiding_naturality_right a b c f := by
    simpa [braidIso] using braid_natural (𝟙 a) f
  braiding_naturality_left f c := by
    simpa [braidIso] using braid_natural f (𝟙 c)
  hexagon_forward a b c := by
    apply (Arrow.mk_inj _ _).1
    simp only [braidIso, associator_eq, eqToIso.hom, whiskerRight_eq, whiskerLeft_eq,
      tensorObj_eq, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
    exact hexagon a b c
  hexagon_reverse a b c := by
    apply (Arrow.mk_inj _ _).1
    simp only [braidIso, associator_eq, eqToIso.inv, whiskerRight_eq, whiskerLeft_eq,
      tensorObj_eq, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
    exact hexagon_reverse a b c
  symmetry a b := braid_braid a b

@[simp] theorem braiding_hom_eq (a b : C) : (β_ a b).hom = σ_ a b := rfl
@[simp] theorem braiding_inv_eq (a b : C) : (β_ a b).inv = σ_ b a := rfl

end StrictSMC

end FreeMarkov

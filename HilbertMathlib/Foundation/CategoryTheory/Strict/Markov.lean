/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/Strict/Markov.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: `ε_1 = 1`, `δ_1 = 1`, and the Markov part of the
bridge to Mathlib.
-/
module

public import HilbertMathlib.Foundation.CategoryTheory.Strict.Bridge

@[expose] public section

universe v u

namespace FreeMarkov

open CategoryTheory MonoidalCategory StrictSMC StrictMarkov ComonObj

namespace StrictMarkov

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]

variable (C)

/-- The comonoid `(a, δ_a, ε_a)` as a Mathlib comonoid object. -/
instance comonObj (a : C) : ComonObj a where
  counit := ε_ a
  comul := δ_ a
  counit_comul := by
    apply (Arrow.mk_inj _ _).1
    simpa using discard_copy a
  comul_counit := by
    apply (Arrow.mk_inj _ _).1
    simpa using copy_discard a
  comul_assoc := by
    apply (Arrow.mk_inj _ _).1
    simp only [whiskerLeft_eq, whiskerRight_eq, associator_eq, eqToIso.hom, tensorObj_eq]
    rw [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    exact (copy_assoc a).symm

instance isCommComonObj (a : C) : IsCommComonObj a where
  comul_comm := copy_comm a

/-- **Bridge, Markov part.** A strict Markov category is a Mathlib Markov category,
whose monoidal structure is `StrictSMC.monoidalCategory` (associators and unitors
`eqToIso`), whose braiding is `σ`, and whose copy and discard are `δ` and `ε`. -/
instance markovCategory : MarkovCategory C where
  toSymmetricCategory := StrictSMC.symmetricCategory C
  comonObj := comonObj C
  isCommComonObj := isCommComonObj C
  copy_tensor a b := by
    apply (Arrow.mk_inj _ _).1
    simp only [tensorμ, tensorObj_eq, tensorHom_eq, whiskerLeft_eq, whiskerRight_eq,
      associator_eq, eqToIso.hom, eqToIso.inv, braiding_hom_eq, id_tensorHom_eqToHom]
    change Arrow.mk (δ_ (a * b)) = _
    rw [copy_tensor]
    simp only [eqToHom_trans_assoc]
    refine Arrow.mk_comp_congr rfl ?_
    simp only [Arrow.arrow_mk_eqToHom_comp, eqToHom_trans, Arrow.arrow_mk_comp_eqToHom]
    exact tensorHom_assoc (𝟙 a) (σ_ a b) (𝟙 b)
  discard_tensor a b := by
    apply (Arrow.mk_inj _ _).1
    simp only [tensorObj_eq, tensorHom_eq, leftUnitor_eq, eqToIso.hom,
      Arrow.arrow_mk_comp_eqToHom]
    exact discard_tensor a b
  copy_unit := by
    apply (Arrow.mk_inj _ _).1
    simp only [tensorUnit_eq, leftUnitor_eq, eqToIso.inv, Arrow.mk_eqToHom]
    exact copy_one
  discard_unit := discard_one
  discard_natural f := discard_natural f

variable {C}

@[simp] theorem comul_eq (a : C) : Δ[a] = δ_ a := rfl
@[simp] theorem counit_eq (a : C) : ε[a] = ε_ a := rfl

end StrictMarkov

end FreeMarkov

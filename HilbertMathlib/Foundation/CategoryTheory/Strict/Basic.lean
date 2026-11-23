/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/Strict/Basic.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: strict symmetric monoidal categories and strict
Markov categories (Introduction of the paper).

Encoding (design decision D2 of `formalization/PLAN.md`): the objects of a strict
monoidal category form a monoid `C`, with `a ⊗ b` the product `a * b` and the unit
the identity `1`; the tensor product of morphisms is `f ⊗ₛ g : a * c ⟶ b * d`.
Laws whose two sides have types that differ only by `mul_assoc`, `one_mul`,
`mul_one` are stated as equations in `Arrow C` (see `FreeMarkov.Stage0.Arrow`).
Where a composite itself has to pass through such an identification (the hexagon,
the compatibility of duplicates with `⊗`), the identification is an `eqToHom`.
-/
module

public import HilbertMathlib.Foundation.CategoryTheory.Arrow
public import HilbertMathlib.Foundation.CategoryTheory.GraphMonoid

@[expose] public section

universe v u

namespace FreeMarkov

open CategoryTheory

/-- A **symmetric strict monoidal category** whose monoid of objects is `C`.

*Introduction.* "Let `C` be a symmetric monoidal category; the monoidal unit is
denoted by `1` ..."; a strict one has identity associators and unitors, so its
objects form a monoid under `⊗`.  The axioms below are those of a symmetric
monoidal category (bifunctoriality of `⊗`, naturality of the symmetry `σ`, one
hexagon, `σ_{b,a} ∘ σ_{a,b} = 1`) with the associators and unitors identities.
The second hexagon is a theorem (`StrictSMC.hexagon_reverse`). -/
class StrictSMC (C : Type u) [Monoid C] [Category.{v} C] where
  /-- The monoidal product of morphisms, `f ⊗ g`. -/
  tensorHom {a b c d : C} : (a ⟶ b) → (c ⟶ d) → (a * c ⟶ b * d)
  /-- The symmetry `σ_{a,b} : a ⊗ b → b ⊗ a`. -/
  braid (a b : C) : a * b ⟶ b * a
  tensorHom_id (a c : C) : tensorHom (𝟙 a) (𝟙 c) = 𝟙 (a * c)
  tensorHom_comp {a₁ a₂ a₃ c₁ c₂ c₃ : C} (f : a₁ ⟶ a₂) (f' : a₂ ⟶ a₃) (g : c₁ ⟶ c₂)
    (g' : c₂ ⟶ c₃) : tensorHom (f ≫ f') (g ≫ g') = tensorHom f g ≫ tensorHom f' g'
  /-- `(f ⊗ g) ⊗ h = f ⊗ (g ⊗ h)`. -/
  tensorHom_assoc {a b c d e f : C} (x : a ⟶ b) (y : c ⟶ d) (z : e ⟶ f) :
    Arrow.mk (tensorHom (tensorHom x y) z) = Arrow.mk (tensorHom x (tensorHom y z))
  /-- `1_1 ⊗ f = f`. -/
  id_one_tensorHom {a b : C} (f : a ⟶ b) : Arrow.mk (tensorHom (𝟙 (1 : C)) f) = Arrow.mk f
  /-- `f ⊗ 1_1 = f`. -/
  tensorHom_id_one {a b : C} (f : a ⟶ b) : Arrow.mk (tensorHom f (𝟙 (1 : C))) = Arrow.mk f
  /-- Naturality of the symmetry. -/
  braid_natural {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) :
    tensorHom f g ≫ braid b d = braid a c ≫ tensorHom g f
  /-- `σ_{b,a} ∘ σ_{a,b} = 1`. -/
  braid_braid (a b : C) : braid a b ≫ braid b a = 𝟙 (a * b)
  /-- The hexagon: `σ_{a, b⊗c} = (1_b ⊗ σ_{a,c}) ∘ (σ_{a,b} ⊗ 1_c)`. -/
  hexagon (a b c : C) :
    Arrow.mk (braid a (b * c)) =
      Arrow.mk (tensorHom (braid a b) (𝟙 c) ≫ eqToHom (mul_assoc b a c) ≫
        tensorHom (𝟙 b) (braid a c))

namespace StrictSMC

@[inherit_doc] scoped infixr:70 " ⊗ₛ " => StrictSMC.tensorHom
@[inherit_doc] scoped notation "σ_" => StrictSMC.braid

end StrictSMC

open StrictSMC

/-- A **strict Markov category** whose monoid of objects is `C`.

*Introduction.* "Suppose that for each object `A ∈ C` there are distinguished
arrows `δ_A : A → A ⊗ A`, called the duplicate on `A`, and `ε_A : A → 1`, called
the discard on `A`, that form a cocommutative monoidal comonoid as depicted in
(1.1) ... Moreover, they respect the monoidal product (1.2) ... we call `C` a
**Markov category** if the discards are natural (1.3) ...  A Markov category is
**strict** if its underlying monoidal category is."

The equations `ε_1 = 1_1` and `δ_1 = 1_1` are not axioms; they are the theorems
`StrictMarkov.discard_one` and `StrictMarkov.copy_one` (the paper cites Fritz,
Remark 2.3, for them). -/
class StrictMarkov (C : Type u) [Monoid C] [Category.{v} C] extends StrictSMC C where
  /-- The duplicate `δ_a`. -/
  copy (a : C) : a ⟶ a * a
  /-- The discard `ε_a`. -/
  discard (a : C) : a ⟶ 1
  /-- (1.1), coassociativity: `(δ_a ⊗ 1_a) ∘ δ_a = (1_a ⊗ δ_a) ∘ δ_a`. -/
  copy_assoc (a : C) :
    Arrow.mk (copy a ≫ tensorHom (copy a) (𝟙 a)) = Arrow.mk (copy a ≫ tensorHom (𝟙 a) (copy a))
  /-- (1.1), counitality: `(ε_a ⊗ 1_a) ∘ δ_a = 1_a`. -/
  discard_copy (a : C) : Arrow.mk (copy a ≫ tensorHom (discard a) (𝟙 a)) = Arrow.mk (𝟙 a)
  /-- (1.1), counitality: `(1_a ⊗ ε_a) ∘ δ_a = 1_a`. -/
  copy_discard (a : C) : Arrow.mk (copy a ≫ tensorHom (𝟙 a) (discard a)) = Arrow.mk (𝟙 a)
  /-- (1.1), cocommutativity: `σ_{a,a} ∘ δ_a = δ_a`. -/
  copy_comm (a : C) : copy a ≫ braid a a = copy a
  /-- (1.2): `δ_{a⊗b} = (1_a ⊗ σ_{a,b} ⊗ 1_b) ∘ (δ_a ⊗ δ_b)`. -/
  copy_tensor (a b : C) :
    Arrow.mk (copy (a * b)) =
      Arrow.mk (tensorHom (copy a) (copy b) ≫
        eqToHom (by simp only [mul_assoc] : a * a * (b * b) = a * (a * b) * b) ≫
        tensorHom (tensorHom (𝟙 a) (braid a b)) (𝟙 b))
  /-- (1.2): `ε_{a⊗b} = ε_a ⊗ ε_b`. -/
  discard_tensor (a b : C) : Arrow.mk (discard (a * b)) = Arrow.mk (tensorHom (discard a) (discard b))
  /-- (1.3), naturality of discards: `ε_b ∘ f = ε_a`. -/
  discard_natural {a b : C} (f : a ⟶ b) : f ≫ discard b = discard a

namespace StrictMarkov

@[inherit_doc] scoped notation "δ_" => StrictMarkov.copy
@[inherit_doc] scoped notation "ε_" => StrictMarkov.discard

end StrictMarkov

end FreeMarkov

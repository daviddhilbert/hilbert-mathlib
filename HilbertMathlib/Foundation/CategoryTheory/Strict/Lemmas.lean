/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/Strict/Lemmas.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: elementary consequences of the axioms of a
symmetric strict monoidal category, in the `Arrow` calculus.
-/
module

public import HilbertMathlib.Foundation.CategoryTheory.Strict.Basic

@[expose] public section

universe v u

namespace FreeMarkov

open CategoryTheory StrictSMC

namespace StrictSMC

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictSMC C]

/-- Equality in `Arrow C` is a congruence for `⊗`. -/
theorem mk_tensorHom_congr {a b c d a' b' c' d' : C} {f : a ⟶ b} {g : c ⟶ d}
    {f' : a' ⟶ b'} {g' : c' ⟶ d'} (hf : Arrow.mk f = Arrow.mk f')
    (hg : Arrow.mk g = Arrow.mk g') : Arrow.mk (f ⊗ₛ g) = Arrow.mk (f' ⊗ₛ g') := by
  obtain ⟨rfl, rfl, rfl⟩ := (Arrow.mk_eq_mk_iff _ _).1 hf
  obtain ⟨rfl, rfl, rfl⟩ := (Arrow.mk_eq_mk_iff _ _).1 hg
  simp

@[simp]
theorem tensorHom_eqToHom {a a' c c' : C} (h : a = a') (h' : c = c') :
    eqToHom h ⊗ₛ eqToHom h' = eqToHom (by rw [h, h']) := by
  subst h h'
  simp [tensorHom_id]

@[simp]
theorem id_tensorHom_eqToHom {a c c' : C} (h' : c = c') :
    𝟙 a ⊗ₛ eqToHom h' = eqToHom (by rw [h']) := by
  subst h'
  simp [tensorHom_id]

@[simp]
theorem eqToHom_tensorHom_id {a a' c : C} (h : a = a') :
    eqToHom h ⊗ₛ 𝟙 c = eqToHom (by rw [h]) := by
  subst h
  simp [tensorHom_id]

@[reassoc]
theorem tensorHom_comp' {a₁ a₂ a₃ c₁ c₂ c₃ : C} (f : a₁ ⟶ a₂) (f' : a₂ ⟶ a₃) (g : c₁ ⟶ c₂)
    (g' : c₂ ⟶ c₃) : (f ⊗ₛ g) ≫ (f' ⊗ₛ g') = (f ≫ f') ⊗ₛ (g ≫ g') :=
  (tensorHom_comp f f' g g').symm

@[reassoc (attr := simp)]
theorem braid_braid' (a b : C) : σ_ a b ≫ σ_ b a = 𝟙 (a * b) := braid_braid a b

/-- The second hexagon, `σ_{a⊗b, c} = (σ_{a,c} ⊗ 1_b) ∘ (1_a ⊗ σ_{b,c})`, from the
first one and `σ ∘ σ = 1`. -/
theorem hexagon_reverse (a b c : C) :
    Arrow.mk (σ_ (a * b) c) =
      Arrow.mk ((𝟙 a ⊗ₛ σ_ b c) ≫ eqToHom (mul_assoc a c b).symm ≫ (σ_ a c ⊗ₛ 𝟙 b)) := by
  -- `R` is the right-hand side of the first hexagon for `σ_{c, a⊗b}`, `R'` the
  -- claimed value of its inverse.
  set R := (σ_ c a ⊗ₛ 𝟙 b) ≫ eqToHom (mul_assoc a c b) ≫ (𝟙 a ⊗ₛ σ_ c b) with hR
  set R' := (𝟙 a ⊗ₛ σ_ b c) ≫ eqToHom (mul_assoc a c b).symm ≫ (σ_ a c ⊗ₛ 𝟙 b) with hR'
  have hRR' : R ≫ R' = 𝟙 _ := by
    simp only [hR, hR', Category.assoc, tensorHom_comp'_assoc, Category.id_comp,
      braid_braid', tensorHom_id, eqToHom_trans_assoc, eqToHom_refl]
    rw [tensorHom_comp', braid_braid', Category.comp_id, tensorHom_id]
  have hex := Arrow.comp_eqToHom_eq_of_mk_eq (hexagon c a b) (mul_assoc c a b).symm
    (mul_assoc a b c)
  have key : σ_ (a * b) c ≫ eqToHom (mul_assoc c a b).symm ≫ R ≫ R' =
      eqToHom (mul_assoc a b c) ≫ R' := by
    rw [← Category.assoc (eqToHom _) R R', ← hex]
    simp
  calc Arrow.mk (σ_ (a * b) c)
      = Arrow.mk (σ_ (a * b) c ≫ eqToHom (mul_assoc c a b).symm ≫ R ≫ R') := by
        rw [hRR', Category.comp_id, Arrow.arrow_mk_comp_eqToHom]
    _ = Arrow.mk R' := by rw [key, Arrow.arrow_mk_eqToHom_comp]

end StrictSMC

open StrictMarkov

namespace StrictMarkov

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]

/-- *Introduction.* "the naturality of discards, together with the other conditions
stipulated above, implies that `1` is terminal, and hence `ε_1 = 1_1`."
(Fritz 2020, Remark 2.3; proved here, not assumed.) -/
theorem discard_one : ε_ (1 : C) = 𝟙 1 := by
  -- `1_1 = (ε_1 ⊗ 1_1) ∘ δ_1 = ε_{1⊗1} ∘ δ_1 = ε_1`.
  have h₁ : Arrow.mk (ε_ (1 : C) ⊗ₛ 𝟙 1) = Arrow.mk (ε_ ((1 : C) * 1)) := by
    rw [tensorHom_id_one, mul_one]
  have h₂ : Arrow.mk (𝟙 (1 : C)) = Arrow.mk (ε_ (1 : C)) := by
    rw [← discard_copy, Arrow.mk_comp_congr rfl h₁, discard_natural]
  exact (Arrow.eq_of_mk_eq h₂).symm

/-- *Introduction.* "Also note that `δ_1 = 1_1` in any strict Markov category."
(Fritz 2020, Remark 2.3; proved here, not assumed.) -/
theorem copy_one : Arrow.mk (δ_ (1 : C)) = Arrow.mk (𝟙 (1 : C)) := by
  -- `δ_1 = (1_1 ⊗ ε_1) ∘ δ_1 = 1_1`.
  have h := copy_discard (1 : C)
  rwa [discard_one, tensorHom_id, Category.comp_id] at h

/-- *Introduction.* The unit `1` is terminal: every morphism into it is a discard. -/
theorem eq_discard {a : C} (f : a ⟶ 1) : f = ε_ a := by
  rw [← discard_natural f, discard_one, Category.comp_id]

end StrictMarkov

end FreeMarkov

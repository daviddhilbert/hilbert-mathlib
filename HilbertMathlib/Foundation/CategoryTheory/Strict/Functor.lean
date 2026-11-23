/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/Strict/Functor.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: strict functors, the underlying graph monoid of a
strict monoidal category (Introduction of the paper).
-/
module

public import HilbertMathlib.Foundation.CategoryTheory.Strict.Lemmas

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ v u

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov

/-- Equality in `Arrow` is preserved by functors. -/
theorem _root_.CategoryTheory.Functor.mk_map_congr {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) {a b a' b' : C} {f : a ⟶ b} {f' : a' ⟶ b'}
    (h : Arrow.mk f = Arrow.mk f') : Arrow.mk (F.map f) = Arrow.mk (F.map f') := by
  obtain ⟨rfl, rfl, rfl⟩ := (Arrow.mk_eq_mk_iff _ _).1 h
  simp

/-- *Introduction.* "If `D` is a strict Markov category then `D₀` is a monoid under
`⊗`, and hence the underlying graph of `D` is a graph monoid."  Its vertices are
the objects of `D`, its arrows all morphisms of `D`. -/
@[reducible] def graphMonoid (D : Type u) [Monoid D] [Category.{v} D] : GraphMonoid.{u, max u v} where
  V := D
  A := Arrow D
  s f := f.left
  t f := f.right

/-- A **strict symmetric monoidal functor**: a strong symmetric monoidal functor whose
structure isomorphisms are identities.  So `F(a ⊗ b) = F a ⊗ F b`, `F 1 = 1`,
`F(f ⊗ g) = F f ⊗ F g` and `F σ_{a,b} = σ_{F a, F b}`. -/
structure StrictFunctor (C : Type u₁) [Monoid C] [Category.{v₁} C] [StrictSMC C]
    (D : Type u₂) [Monoid D] [Category.{v₂} D] [StrictSMC D] extends Functor C D where
  obj_one : obj 1 = 1
  obj_mul (a b : C) : obj (a * b) = obj a * obj b
  map_tensorHom {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) :
    Arrow.mk (map (f ⊗ₛ g)) = Arrow.mk (map f ⊗ₛ map g)
  map_braid (a b : C) : Arrow.mk (map (σ_ a b)) = Arrow.mk (σ_ (obj a) (obj b))

/-- *Introduction.* A **strict Markov functor**: "a Markov functor is a strong
symmetric monoidal functor `F : C → D` between two Markov categories that preserves
the distinguished comonoids by way of matching duplicates and discards ... a Markov
functor is **strict** if its structure isomorphisms are identities."  So
`F δ_a = δ_{F a}` and `F ε_a = ε_{F a}`.  (The paper notes that the discards are
matched automatically; see `StrictMarkovFunctor.ofMapCopy`.) -/
structure StrictMarkovFunctor (C : Type u₁) [Monoid C] [Category.{v₁} C] [StrictMarkov C]
    (D : Type u₂) [Monoid D] [Category.{v₂} D] [StrictMarkov D] extends StrictFunctor C D where
  map_copy (a : C) : Arrow.mk (map (δ_ a)) = Arrow.mk (δ_ (obj a))
  map_discard (a : C) : Arrow.mk (map (ε_ a)) = Arrow.mk (ε_ (obj a))

namespace StrictFunctor

variable {C : Type u₁} [Monoid C] [Category.{v₁} C] [StrictSMC C]
  {D : Type u₂} [Monoid D] [Category.{v₂} D] [StrictSMC D]
  {E : Type u₃} [Monoid E] [Category.{v₃} E] [StrictSMC E]

/-- The object map of a strict functor, as a monoid homomorphism. -/
def objHom (F : StrictFunctor C D) : C →* D where
  toFun := F.obj
  map_one' := F.obj_one
  map_mul' := F.obj_mul

/-- The graph monoid homomorphism between underlying graph monoids induced by a
strict functor. -/
def toGraphMonoidHom (F : StrictFunctor C D) : (graphMonoid C).Hom (graphMonoid D) where
  V := F.objHom
  A f := Arrow.mk (F.map f.hom)
  s_A _ := rfl
  t_A _ := rfl

@[simp] theorem toGraphMonoidHom_V_apply (F : StrictFunctor C D) (a : C) :
    F.toGraphMonoidHom.V a = F.obj a := rfl

@[simp] theorem toGraphMonoidHom_A (F : StrictFunctor C D) (f : Arrow C) :
    F.toGraphMonoidHom.A f = Arrow.mk (F.map f.hom) := rfl

/-- Strict functors are determined by their underlying functors. -/
theorem ext_toFunctor {F G : StrictFunctor C D} (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F; cases G; cases h; rfl

/-- Strict functors are determined by their values on morphisms, compared in `Arrow D`. -/
theorem ext {F G : StrictFunctor C D}
    (h : ∀ {a b : C} (f : a ⟶ b), Arrow.mk (F.map f) = Arrow.mk (G.map f)) : F = G := by
  have hobj : ∀ a, F.obj a = G.obj a := fun a => Arrow.left_eq_of_mk_eq (h (𝟙 a))
  refine ext_toFunctor (CategoryTheory.Functor.ext hobj fun a b f => ?_)
  obtain ⟨_, _, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 (h f)
  exact hf

/-- The identity strict functor. -/
def id (C : Type u₁) [Monoid C] [Category.{v₁} C] [StrictSMC C] : StrictFunctor C C where
  toFunctor := 𝟭 C
  obj_one := rfl
  obj_mul _ _ := rfl
  map_tensorHom _ _ := rfl
  map_braid _ _ := rfl

/-- Composition of strict functors; `G.comp F` is "`G ∘ F`". -/
def comp (G : StrictFunctor D E) (F : StrictFunctor C D) : StrictFunctor C E where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  obj_one := by simp [F.obj_one, G.obj_one]
  obj_mul a b := by simp [F.obj_mul, G.obj_mul]
  map_tensorHom f g := (G.toFunctor.mk_map_congr (F.map_tensorHom f g)).trans
    (G.map_tensorHom _ _)
  map_braid a b := (G.toFunctor.mk_map_congr (F.map_braid a b)).trans (G.map_braid _ _)

end StrictFunctor

namespace StrictMarkovFunctor

variable {C : Type u₁} [Monoid C] [Category.{v₁} C] [StrictMarkov C]
  {D : Type u₂} [Monoid D] [Category.{v₂} D] [StrictMarkov D]
  {E : Type u₃} [Monoid E] [Category.{v₃} E] [StrictMarkov E]

/-- The graph monoid homomorphism induced by a strict Markov functor. -/
abbrev toGraphMonoidHom (F : StrictMarkovFunctor C D) : (graphMonoid C).Hom (graphMonoid D) :=
  F.toStrictFunctor.toGraphMonoidHom

/-- Strict Markov functors are determined by their underlying strict functors. -/
theorem ext_toStrictFunctor {F G : StrictMarkovFunctor C D}
    (h : F.toStrictFunctor = G.toStrictFunctor) : F = G := by
  cases F; cases G; cases h; rfl

/-- *Introduction.* "Of course the discards are matched automatically, since `1` is
terminal": a strict functor between strict Markov categories that matches
duplicates is a strict Markov functor. -/
def ofMapCopy (F : StrictFunctor C D)
    (h : ∀ a : C, Arrow.mk (F.map (δ_ a)) = Arrow.mk (δ_ (F.obj a))) :
    StrictMarkovFunctor C D where
  toStrictFunctor := F
  map_copy := h
  map_discard a := by
    rw [← Arrow.arrow_mk_comp_eqToHom (F.map (ε_ a)) F.obj_one,
      eq_discard (F.map (ε_ a) ≫ eqToHom F.obj_one)]

/-- The identity strict Markov functor. -/
def id (C : Type u₁) [Monoid C] [Category.{v₁} C] [StrictMarkov C] : StrictMarkovFunctor C C where
  toStrictFunctor := StrictFunctor.id C
  map_copy _ := rfl
  map_discard _ := rfl

/-- Composition of strict Markov functors. -/
def comp (G : StrictMarkovFunctor D E) (F : StrictMarkovFunctor C D) : StrictMarkovFunctor C E where
  toStrictFunctor := G.toStrictFunctor.comp F.toStrictFunctor
  map_copy a := (G.toFunctor.mk_map_congr (F.map_copy a)).trans (G.map_copy _)
  map_discard a := (G.toFunctor.mk_map_congr (F.map_discard a)).trans (G.map_discard _)

end StrictMarkovFunctor

end FreeMarkov

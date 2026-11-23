/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/Syntactic/Universal.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: the universal property of `Syn_s(G)` and the
generation principle (design decision D4 of `formalization/PLAN.md`).
-/
module

public import HilbertMathlib.Foundation.CategoryTheory.Syntactic.Basic

@[expose] public section

universe w v u' v'

namespace FreeMarkov

open CategoryTheory StrictSMC

namespace FreeGraphMonoid.Syn

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- **Generation principle.** Every morphism of `Syn_s(G)` is built from the
generators, identities and symmetries by composition and monoidal product: a
property of morphisms that holds for these and is closed under `∘` and `⊗` holds
for all morphisms.

(PLAN.md, Section 2: "Every morphism of `F_s(G)` is built from the generators,
identities and symmetries by composition and monoidal product.") -/
theorem induction {P : ∀ {a b : G.Syn}, (a ⟶ b) → Prop}
    (h_gen : ∀ x : G.A, P (gen x))
    (h_id : ∀ a : G.Syn, P (𝟙 a))
    (h_braid : ∀ a b : G.Syn, P (σ_ a b))
    (h_comp : ∀ {a b c : G.Syn} (f : a ⟶ b) (g : b ⟶ c), P f → P g → P (f ≫ g))
    (h_tensor : ∀ {a b c d : G.Syn} (f : a ⟶ b) (g : c ⟶ d), P f → P g → P (f ⊗ₛ g))
    {a b : G.Syn} (f : a ⟶ b) : P f := by
  have key : ∀ {a b : FreeMonoid S} (t : G.Term a b), P (ofTerm t) := by
    intro a b t
    induction t with
    | gen x => exact h_gen x
    | id a => exact h_id a
    | comp t u iht ihu => exact h_comp _ _ iht ihu
    | tensor t u iht ihu => exact h_tensor _ _ iht ihu
    | braid a b => exact h_braid a b
  exact Quotient.inductionOn (motive := fun q : Quotient (G.homSetoid a b) => P q) f key

variable {D : Type u'} [Monoid D] [Category.{v'} D] [StrictSMC D]
  (f : G.toGraphMonoid.Hom (graphMonoid D))

/-- The value of a term in `D` along a graph monoid homomorphism `f`. -/
def interp : ∀ {a b : FreeMonoid S}, G.Term a b → (f.V a ⟶ f.V b)
  | _, _, .gen x => eqToHom (f.s_A x).symm ≫ (f.A x).hom ≫ eqToHom (f.t_A x)
  | _, _, .id a => 𝟙 (f.V a)
  | _, _, .comp t u => interp t ≫ interp u
  | _, _, .tensor t u => eqToHom (f.V.map_mul _ _) ≫ (interp t ⊗ₛ interp u) ≫
      eqToHom (f.V.map_mul _ _).symm
  | _, _, .braid a b => eqToHom (f.V.map_mul a b) ≫ σ_ (f.V a) (f.V b) ≫
      eqToHom (f.V.map_mul b a).symm

theorem arrow_interp_gen (x : G.A) : Arrow.mk (interp f (Term.gen x)) = f.A x := by
  simp only [interp, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom, Arrow.mk_eq]

theorem arrow_interp_tensor {a b c d : FreeMonoid S} (t : G.Term a b) (u : G.Term c d) :
    Arrow.mk (interp f (t.tensor u)) = Arrow.mk (interp f t ⊗ₛ interp f u) := by
  simp only [interp, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]

theorem arrow_interp_braid (a b : FreeMonoid S) :
    Arrow.mk (interp f (Term.braid (G := G) a b)) = Arrow.mk (σ_ (f.V a) (f.V b)) := by
  simp only [interp, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]

theorem arrow_interp_cast {a b a' b' : FreeMonoid S} (ha : a = a') (hb : b = b')
    (t : G.Term a b) : Arrow.mk (interp f (t.cast ha hb)) = Arrow.mk (interp f t) := by
  subst ha hb
  rfl

/-- **Soundness.** Terms related by the axioms have the same value. -/
theorem interp_sound {a b a' b' : FreeMonoid S} {t : G.Term a b} {t' : G.Term a' b'}
    (h : G.Rel t t') : Arrow.mk (interp f t) = Arrow.mk (interp f t') := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | comp _ _ ih ih' => exact Arrow.mk_comp_congr ih ih'
  | tensor _ _ ih ih' =>
    rw [arrow_interp_tensor, arrow_interp_tensor]
    exact mk_tensorHom_congr ih ih'
  | comp_assoc t u w =>
    simp only [interp, Category.assoc]
  | id_comp t =>
    simp only [interp, Category.id_comp]
  | comp_id t =>
    simp only [interp, Category.comp_id]
  | tensor_id a c =>
    rw [arrow_interp_tensor]
    simp only [interp, tensorHom_id]
    exact Arrow.mk_id_congr (f.V.map_mul a c).symm
  | tensor_comp t t' u u' =>
    rw [arrow_interp_tensor]
    simp only [interp, tensorHom_comp]
    exact Arrow.mk_comp_congr (arrow_interp_tensor f t u).symm (arrow_interp_tensor f t' u').symm
  | tensor_assoc t u w =>
    rw [arrow_interp_tensor, arrow_interp_tensor]
    refine (mk_tensorHom_congr (arrow_interp_tensor f t u) rfl).trans ?_
    refine Eq.trans ?_ (mk_tensorHom_congr rfl (arrow_interp_tensor f u w)).symm
    exact tensorHom_assoc _ _ _
  | id_one_tensor t =>
    rw [arrow_interp_tensor]
    refine (mk_tensorHom_congr (Arrow.mk_id_congr f.V.map_one) rfl).trans ?_
    exact id_one_tensorHom _
  | tensor_id_one t =>
    rw [arrow_interp_tensor]
    refine (mk_tensorHom_congr rfl (Arrow.mk_id_congr f.V.map_one)).trans ?_
    exact tensorHom_id_one _
  | braid_natural t u =>
    change Arrow.mk (interp f (t.tensor u) ≫ interp f (Term.braid _ _)) =
      Arrow.mk (interp f (Term.braid _ _) ≫ interp f (u.tensor t))
    rw [Arrow.mk_comp_congr (arrow_interp_tensor f t u) (arrow_interp_braid f _ _),
      Arrow.mk_comp_congr (arrow_interp_braid f _ _) (arrow_interp_tensor f u t),
      braid_natural]
  | braid_braid a b =>
    change Arrow.mk (interp f (Term.braid a b) ≫ interp f (Term.braid b a)) = _
    rw [Arrow.mk_comp_congr (arrow_interp_braid f a b) (arrow_interp_braid f b a),
      braid_braid]
    exact Arrow.mk_id_congr (f.V.map_mul a b).symm
  | hexagon a b c =>
    rw [arrow_interp_braid]
    have hl : Arrow.mk (σ_ (f.V a) (f.V (b * c))) = Arrow.mk (σ_ (f.V a) (f.V b * f.V c)) := by
      rw [f.V.map_mul]
    rw [hl, StrictSMC.hexagon]
    simp only [interp]
    refine Arrow.mk_comp_congr ?_ ?_
    · simp only [Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
      exact mk_tensorHom_congr (by simp) rfl
    · rw [arrow_interp_cast]
      simp only [Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom, interp]
      exact mk_tensorHom_congr rfl (by simp)

/-- The strict symmetric monoidal functor `Syn_s(G) → D` induced by `f`. -/
def lift : StrictFunctor G.Syn D where
  obj a := f.V a
  map {a b} := Quotient.lift (interp f (a := a) (b := b))
    fun _ _ h => Arrow.eq_of_mk_eq (interp_sound f h)
  map_id _ := rfl
  map_comp m m' := Quotient.inductionOn₂ m m' fun _ _ => rfl
  obj_one := f.V.map_one
  obj_mul a b := f.V.map_mul a b
  map_tensorHom m m' := Quotient.inductionOn₂ m m' fun t u => arrow_interp_tensor f t u
  map_braid a b := arrow_interp_braid f a b

theorem lift_map_ofTerm {a b : FreeMonoid S} (t : G.Term a b) :
    (lift f).map (ofTerm t) = interp f t := rfl

/-- `lift f` extends `f`. -/
theorem lift_comp_ι : (lift f).toGraphMonoidHom.comp (ι G) = f := by
  ext x
  · rfl
  · exact arrow_interp_gen f x

/-- `lift f` is the only strict functor extending `f`. -/
theorem eq_lift {F : StrictFunctor G.Syn D} (h : F.toGraphMonoidHom.comp (ι G) = f) :
    F = lift f := by
  have hobj : ∀ a : G.Syn, F.obj a = f.V a := fun a => congrArg (fun g => g.V a) h
  have hA : ∀ x : G.A, Arrow.mk (F.map (gen x)) = f.A x := fun x => congrArg (fun g => g.A x) h
  have key : ∀ {a b : FreeMonoid S} (t : G.Term a b),
      Arrow.mk (F.map (ofTerm t)) = Arrow.mk (interp f t) := by
    intro a b t
    induction t with
    | gen x => exact (hA x).trans (arrow_interp_gen f x).symm
    | id a =>
      change Arrow.mk (F.map (𝟙 _)) = _
      rw [F.map_id]
      exact Arrow.mk_id_congr (hobj a)
    | comp t u iht ihu =>
      rw [ofTerm_comp, F.map_comp]
      exact Arrow.mk_comp_congr iht ihu
    | tensor t u iht ihu =>
      refine (F.map_tensorHom (ofTerm t) (ofTerm u)).trans ?_
      rw [arrow_interp_tensor]
      exact mk_tensorHom_congr iht ihu
    | braid a b =>
      refine (F.map_braid a b).trans ?_
      rw [arrow_interp_braid, hobj a, hobj b]
  refine StrictFunctor.ext fun {a b} m => ?_
  exact Quotient.inductionOn (motive := fun q : Quotient (G.homSetoid a b) =>
    Arrow.mk (F.map q) = Arrow.mk ((lift f).map q)) m key

/-- **Universal property of `Syn_s(G)`.** Every graph monoid homomorphism `f` from
`G` to (the underlying graph monoid of) a symmetric strict monoidal category `D`
factors through the inclusion `ι : G → Syn_s(G)` by exactly one strict symmetric
monoidal functor.

This is the syntactic counterpart of the second half of Joyal–Street's
Theorem 2.3 (cited result C1); here it is proved, not assumed. -/
theorem existsUnique_lift :
    ∃! F : StrictFunctor G.Syn D, F.toGraphMonoidHom.comp (ι G) = f :=
  ⟨lift f, lift_comp_ι f, fun _ h => eq_lift f h⟩

variable {f} in
/-- Two strict functors out of `Syn_s(G)` that agree on the generators (and hence
on words) are equal. -/
theorem strictFunctor_ext {F F' : StrictFunctor G.Syn D}
    (h : F.toGraphMonoidHom.comp (ι G) = F'.toGraphMonoidHom.comp (ι G)) : F = F' :=
  (eq_lift _ h).trans (eq_lift _ rfl).symm

end FreeGraphMonoid.Syn

end FreeMarkov

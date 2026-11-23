/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/Syntactic/Basic.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: the syntactic free symmetric strict monoidal
category `Syn_s(G)` on a free graph monoid `G` (design decision D4 of
`formalization/PLAN.md`).

Objects are the words `FreeMonoid S`; morphisms `a ⟶ b` are formal composites and
monoidal products of generators, identities and symmetries, modulo the axioms of
a symmetric strict monoidal category.  Joyal–Street's Theorem 2.3 (the cited
result C1) is stated in Stage 1 as a bijection between these morphisms and classes
of anchored diagrams, and proved for the combinatorial diagrams in Stage 7; freeness of `Syn_s(G)` and the generation
principle are *proved* here.

The pattern (terms modulo the axioms, `lift`, induction on terms) follows
Mathlib's `FreeMonoidalCategory`, Tau Ceti's `TensorSignature.FreeMonoidal` and
Carlier's `FreeSymmetricMonoidalCategory` (all Apache-2.0); no code is copied.
Unlike them, `Syn_s(G)` is strict on unparenthesized words, so its relation is
heterogeneous: it relates terms whose source and target words are only
propositionally equal (e.g. `(f ⊗ g) ⊗ h` and `f ⊗ (g ⊗ h)`).
-/
module

public import HilbertMathlib.Foundation.CategoryTheory.Strict.Free

@[expose] public section

universe w v

namespace FreeMarkov

open CategoryTheory StrictSMC

namespace FreeGraphMonoid

variable {S : Type w} (G : FreeGraphMonoid.{w, v} S)

/-- Terms: formal composites and monoidal products of generators, identities and
symmetries, typed by their source and target words. -/
inductive Term : FreeMonoid S → FreeMonoid S → Type (max w v)
  | gen (x : G.A) : Term (G.s x) (G.t x)
  | id (a : FreeMonoid S) : Term a a
  | comp {a b c : FreeMonoid S} : Term a b → Term b c → Term a c
  | tensor {a b c d : FreeMonoid S} : Term a b → Term c d → Term (a * c) (b * d)
  | braid (a b : FreeMonoid S) : Term (a * b) (b * a)

variable {G}

/-- Retyping a term along equalities of its source and target words. -/
def Term.cast {a b a' b' : FreeMonoid S} (ha : a = a') (hb : b = b') (t : G.Term a b) :
    G.Term a' b' :=
  ha ▸ hb ▸ t

variable (G)

/-- The axioms of a symmetric strict monoidal category, as a congruence on terms.
The relation is heterogeneous: related terms have propositionally equal source
and target words (`Rel.src_eq`, `Rel.tgt_eq`). -/
inductive Rel : ∀ {a b a' b' : FreeMonoid S}, G.Term a b → G.Term a' b' → Prop
  | refl {a b} (t : G.Term a b) : Rel t t
  | symm {a b a' b'} {t : G.Term a b} {t' : G.Term a' b'} : Rel t t' → Rel t' t
  | trans {a b a' b' a'' b''} {t : G.Term a b} {t' : G.Term a' b'} {t'' : G.Term a'' b''} :
      Rel t t' → Rel t' t'' → Rel t t''
  | comp {a b c a' b' c'} {t : G.Term a b} {u : G.Term b c} {t' : G.Term a' b'}
      {u' : G.Term b' c'} : Rel t t' → Rel u u' → Rel (t.comp u) (t'.comp u')
  | tensor {a b c d a' b' c' d'} {t : G.Term a b} {u : G.Term c d} {t' : G.Term a' b'}
      {u' : G.Term c' d'} : Rel t t' → Rel u u' → Rel (t.tensor u) (t'.tensor u')
  | comp_assoc {a b c d} (t : G.Term a b) (u : G.Term b c) (w : G.Term c d) :
      Rel ((t.comp u).comp w) (t.comp (u.comp w))
  | id_comp {a b} (t : G.Term a b) : Rel ((Term.id a).comp t) t
  | comp_id {a b} (t : G.Term a b) : Rel (t.comp (Term.id b)) t
  | tensor_id (a c : FreeMonoid S) : Rel ((Term.id a).tensor (Term.id c)) (Term.id (a * c))
  | tensor_comp {a₁ a₂ a₃ c₁ c₂ c₃} (t : G.Term a₁ a₂) (t' : G.Term a₂ a₃) (u : G.Term c₁ c₂)
      (u' : G.Term c₂ c₃) : Rel ((t.comp t').tensor (u.comp u')) ((t.tensor u).comp (t'.tensor u'))
  | tensor_assoc {a b c d e f} (t : G.Term a b) (u : G.Term c d) (w : G.Term e f) :
      Rel ((t.tensor u).tensor w) (t.tensor (u.tensor w))
  | id_one_tensor {a b} (t : G.Term a b) : Rel ((Term.id 1).tensor t) t
  | tensor_id_one {a b} (t : G.Term a b) : Rel (t.tensor (Term.id 1)) t
  | braid_natural {a b c d} (t : G.Term a b) (u : G.Term c d) :
      Rel ((t.tensor u).comp (Term.braid b d)) ((Term.braid a c).comp (u.tensor t))
  | braid_braid (a b : FreeMonoid S) :
      Rel ((Term.braid a b).comp (Term.braid b a)) (Term.id (a * b))
  | hexagon (a b c : FreeMonoid S) :
      Rel (Term.braid a (b * c))
        (((Term.braid a b).tensor (Term.id c)).comp
          (((Term.id b).tensor (Term.braid a c)).cast (mul_assoc b a c).symm rfl))

/-- The relation, restricted to terms with the same source and target, as a setoid. -/
def homSetoid (a b : FreeMonoid S) : Setoid (G.Term a b) where
  r t t' := G.Rel t t'
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-- The syntactic free symmetric strict monoidal category `Syn_s(G)`: a type synonym
for the words, carrying the category structure. -/
def Syn (_G : FreeGraphMonoid.{w, v} S) : Type w := FreeMonoid S

instance : Monoid G.Syn := inferInstanceAs (Monoid (FreeMonoid S))

/-- A word, regarded as an object of `Syn_s(G)`. -/
def Syn.of (a : FreeMonoid S) : G.Syn := a

instance : Category.{max w v} G.Syn where
  Hom a b := Quotient (G.homSetoid a b)
  id a := ⟦Term.id a⟧
  comp := Quotient.map₂ Term.comp fun _ _ h _ _ h' => Rel.comp h h'
  id_comp f := Quotient.inductionOn f fun t => Quotient.sound (Rel.id_comp t)
  comp_id f := Quotient.inductionOn f fun t => Quotient.sound (Rel.comp_id t)
  assoc f g h := Quotient.inductionOn₃ f g h fun t u w => Quotient.sound (Rel.comp_assoc t u w)

namespace Syn

variable {G}

/-- The morphism of `Syn_s(G)` represented by a term. -/
def ofTerm {a b : FreeMonoid S} (t : G.Term a b) : (Syn.of G a ⟶ Syn.of G b) := ⟦t⟧

theorem ofTerm_eq_ofTerm {a b : FreeMonoid S} {t t' : G.Term a b} (h : G.Rel t t') :
    ofTerm t = ofTerm t' :=
  Quotient.sound h

/-- Related terms have equal source words. -/
theorem _root_.FreeMarkov.FreeGraphMonoid.Rel.src_eq {a b a' b' : FreeMonoid S}
    {t : G.Term a b} {t' : G.Term a' b'} (h : G.Rel t t') : a = a' := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | comp _ _ ih _ => exact ih
  | tensor _ _ ih ih' => rw [ih, ih']
  | tensor_assoc => exact mul_assoc _ _ _
  | id_one_tensor => exact one_mul _
  | tensor_id_one => exact mul_one _
  | hexagon => exact (mul_assoc _ _ _).symm
  | _ => rfl

/-- Related terms have equal target words. -/
theorem _root_.FreeMarkov.FreeGraphMonoid.Rel.tgt_eq {a b a' b' : FreeMonoid S}
    {t : G.Term a b} {t' : G.Term a' b'} (h : G.Rel t t') : b = b' := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | comp _ _ _ ih => exact ih
  | tensor _ _ ih ih' => rw [ih, ih']
  | tensor_assoc => exact mul_assoc _ _ _
  | id_one_tensor => exact one_mul _
  | tensor_id_one => exact mul_one _
  | hexagon => exact mul_assoc _ _ _
  | _ => rfl

/-- Related terms give equal arrows of `Syn_s(G)`. -/
theorem arrow_mk_eq_of_rel {a b a' b' : FreeMonoid S} {t : G.Term a b} {t' : G.Term a' b'}
    (h : G.Rel t t') : Arrow.mk (ofTerm t) = Arrow.mk (ofTerm t') := by
  obtain rfl := h.src_eq
  obtain rfl := h.tgt_eq
  exact congrArg Arrow.mk (ofTerm_eq_ofTerm h)

theorem ofTerm_comp {a b c : FreeMonoid S} (t : G.Term a b) (u : G.Term b c) :
    ofTerm (t.comp u) = ofTerm t ≫ ofTerm u := rfl

theorem id_eq (a : G.Syn) : 𝟙 a = ofTerm (Term.id a) := rfl

theorem eqToHom_comp_ofTerm {a a' b : FreeMonoid S} (h : a' = a) (u : G.Term a b) :
    eqToHom (congrArg (Syn.of G) h) ≫ ofTerm u = ofTerm (u.cast h.symm rfl) := by
  subst h
  exact Category.id_comp _

theorem hexagon_aux (a b c : FreeMonoid S) :
    Arrow.mk (ofTerm (G := G) (Term.braid a (b * c))) =
      Arrow.mk (ofTerm ((Term.braid a b).tensor (Term.id c)) ≫
        eqToHom (congrArg (Syn.of G) (mul_assoc b a c)) ≫
        ofTerm ((Term.id b).tensor (Term.braid a c))) := by
  rw [eqToHom_comp_ofTerm (mul_assoc b a c), ← ofTerm_comp]
  exact arrow_mk_eq_of_rel (Rel.hexagon a b c)

/-- `Syn_s(G)` is a symmetric strict monoidal category. -/
instance strictSMC : StrictSMC G.Syn where
  tensorHom := Quotient.map₂ Term.tensor fun _ _ h _ _ h' => Rel.tensor h h'
  braid a b := ofTerm (Term.braid a b)
  tensorHom_id a c := Quotient.sound (Rel.tensor_id a c)
  tensorHom_comp f f' g g' := Quotient.inductionOn₂ f f' fun t t' =>
    Quotient.inductionOn₂ g g' fun u u' => Quotient.sound (Rel.tensor_comp t t' u u')
  tensorHom_assoc f g h := Quotient.inductionOn₃ f g h fun t u w =>
    arrow_mk_eq_of_rel (Rel.tensor_assoc t u w)
  id_one_tensorHom f := Quotient.inductionOn f fun t => arrow_mk_eq_of_rel (Rel.id_one_tensor t)
  tensorHom_id_one f := Quotient.inductionOn f fun t => arrow_mk_eq_of_rel (Rel.tensor_id_one t)
  braid_natural f g := Quotient.inductionOn₂ f g fun t u =>
    Quotient.sound (Rel.braid_natural t u)
  braid_braid a b := Quotient.sound (Rel.braid_braid a b)
  hexagon a b c := hexagon_aux a b c

theorem ofTerm_tensor {a b c d : FreeMonoid S} (t : G.Term a b) (u : G.Term c d) :
    ofTerm (t.tensor u) = ofTerm t ⊗ₛ ofTerm u := rfl

theorem ofTerm_braid (a b : FreeMonoid S) : ofTerm (Term.braid a b) = σ_ (Syn.of G a) (Syn.of G b) := rfl

/-- The generator `x` as a morphism of `Syn_s(G)`. -/
def gen (x : G.A) : Syn.of G (G.s x) ⟶ Syn.of G (G.t x) := ofTerm (Term.gen x)

variable (G)

/-- The inclusion `G → Syn_s(G)` of the generators: the identity on words, and each
arrow `x` to the morphism `gen x`. -/
def ι : G.toGraphMonoid.Hom (graphMonoid G.Syn) where
  V := MonoidHom.id (FreeMonoid S)
  A x := Arrow.mk (gen x)
  s_A _ := rfl
  t_A _ := rfl

end Syn

end FreeGraphMonoid

end FreeMarkov

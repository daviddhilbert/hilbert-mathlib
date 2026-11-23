/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/GraphMonoid.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: graph monoids (Introduction of the paper).
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic

@[expose] public section

universe w₁ w₂ w₃ w₄ w₅ w₆ u v

namespace FreeMarkov

/-- *Introduction.* "A **graph monoid** is a directed graph `G = (V(G), A(G), s, t)`
whose set of vertices comes with the additional structure of a monoid." -/
structure GraphMonoid where
  /-- The vertices `V(G)`. -/
  V : Type w₁
  /-- The monoid structure on the vertices. -/
  [instMonoid : Monoid V]
  /-- The arrows `A(G)`. -/
  A : Type w₂
  /-- The source of an arrow. -/
  s : A → V
  /-- The target of an arrow. -/
  t : A → V

attribute [instance] GraphMonoid.instMonoid

namespace GraphMonoid

/-- *Introduction.* "A **graph monoid homomorphism** is a graph homomorphism that is
also a homomorphism between the monoids in question." -/
@[ext]
structure Hom (G : GraphMonoid.{w₁, w₂}) (H : GraphMonoid.{w₃, w₄}) where
  /-- The map on vertices, a monoid homomorphism. -/
  V : G.V →* H.V
  /-- The map on arrows. -/
  A : G.A → H.A
  /-- Arrows are mapped compatibly with sources. -/
  s_A (x : G.A) : H.s (A x) = V (G.s x)
  /-- Arrows are mapped compatibly with targets. -/
  t_A (x : G.A) : H.t (A x) = V (G.t x)

namespace Hom

/-- The identity graph monoid homomorphism. -/
def id (G : GraphMonoid.{w₁, w₂}) : Hom G G where
  V := MonoidHom.id G.V
  A := fun x => x
  s_A _ := rfl
  t_A _ := rfl

/-- Composition of graph monoid homomorphisms; `g.comp f` is "`g ∘ f`". -/
def comp {G : GraphMonoid.{w₁, w₂}} {H : GraphMonoid.{w₃, w₄}} {K : GraphMonoid.{w₅, w₆}}
    (g : Hom H K) (f : Hom G H) : Hom G K where
  V := g.V.comp f.V
  A := fun x => g.A (f.A x)
  s_A x := by simp [g.s_A, f.s_A]
  t_A x := by simp [g.t_A, f.t_A]

@[simp] theorem comp_V {G : GraphMonoid.{w₁, w₂}} {H : GraphMonoid.{w₃, w₄}}
    {K : GraphMonoid.{w₅, w₆}} (g : Hom H K) (f : Hom G H) : (g.comp f).V = g.V.comp f.V := rfl

@[simp] theorem comp_A {G : GraphMonoid.{w₁, w₂}} {H : GraphMonoid.{w₃, w₄}}
    {K : GraphMonoid.{w₅, w₆}} (g : Hom H K) (f : Hom G H) (x : G.A) :
    (g.comp f).A x = g.A (f.A x) := rfl

end Hom

/-- *Introduction.* For a set `S`, "let `W(S)` denote the free monoid of words over
(the alphabet) `S`. It is a graph monoid, with the trivial directed graph structure
(no arrows)." -/
def words (S : Type u) : GraphMonoid.{u, 0} where
  V := FreeMonoid S
  A := PEmpty
  s := PEmpty.elim
  t := PEmpty.elim

/-- *Introduction.* "A **free graph monoid** is a triple `(G, S, g)`, where `G` is a
graph monoid and `g : S → V(G)` is an injection, such that the monoid `V(G)` is
isomorphic to the free monoid `W(S)` over `g`."

We read "isomorphic over `g`" as: the monoid homomorphism `W(S) → V(G)` extending
`g` is bijective. -/
structure IsFreeOn (G : GraphMonoid.{w₁, w₂}) {S : Type u} (g : S → G.V) : Prop where
  injective : Function.Injective g
  bijective_lift : Function.Bijective (FreeMonoid.lift g)

end GraphMonoid

/-- A free graph monoid whose monoid of vertices *is* the free monoid `W(S)`.

*Introduction.* "We usually just say `G` is a free graph monoid and leave `S`, `g`
implicit in notation when they are not needed in the discussion. Also it is
harmless to treat `S` as if it is a subset of `V(G)`."  Following this, the
formalization works with `V(G) = W(S)` itself; `GraphMonoid.IsFreeOn.exists_iso`
justifies the identification. -/
structure FreeGraphMonoid (S : Type u) where
  /-- The arrows. -/
  A : Type v
  /-- The source word of an arrow. -/
  s : A → FreeMonoid S
  /-- The target word of an arrow. -/
  t : A → FreeMonoid S

namespace FreeGraphMonoid

variable {S : Type u}

/-- The underlying graph monoid of a free graph monoid. -/
@[reducible] def toGraphMonoid (G : FreeGraphMonoid.{u, v} S) : GraphMonoid.{u, v} where
  V := FreeMonoid S
  A := G.A
  s := G.s
  t := G.t

/-- A `FreeGraphMonoid` is a free graph monoid in the sense of the paper, over the
inclusion of the letters. -/
theorem isFreeOn (G : FreeGraphMonoid.{u, v} S) :
    G.toGraphMonoid.IsFreeOn (FreeMonoid.of : S → FreeMonoid S) := by
  have h : FreeMonoid.lift (FreeMonoid.of : S → FreeMonoid S) = MonoidHom.id _ :=
    FreeMonoid.hom_eq fun x => by simp
  refine ⟨FreeMonoid.of_injective, ?_⟩
  change Function.Bijective (FreeMonoid.lift (FreeMonoid.of : S → FreeMonoid S))
  rw [h]
  exact Function.bijective_id

end FreeGraphMonoid

/-- Every free graph monoid `(G, S, g)` in the sense of the paper is isomorphic, by
graph monoid homomorphisms inverse to each other that are compatible with `g` and
the inclusion of the letters, to a `FreeGraphMonoid S`. -/
theorem GraphMonoid.IsFreeOn.exists_iso {G : GraphMonoid.{w₁, w₂}} {S : Type u}
    {g : S → G.V} (hG : G.IsFreeOn g) :
    ∃ (G' : FreeGraphMonoid.{u, w₂} S) (φ : G.Hom G'.toGraphMonoid)
      (ψ : G'.toGraphMonoid.Hom G),
      ψ.comp φ = Hom.id G ∧ φ.comp ψ = Hom.id G'.toGraphMonoid ∧
        ∀ a, φ.V (g a) = FreeMonoid.of a := by
  let e : FreeMonoid S ≃* G.V := MulEquiv.ofBijective (FreeMonoid.lift g) hG.bijective_lift
  refine ⟨⟨G.A, fun x => e.symm (G.s x), fun x => e.symm (G.t x)⟩,
    ⟨e.symm.toMonoidHom, fun x => x, fun _ => rfl, fun _ => rfl⟩,
    ⟨e.toMonoidHom, fun x => x, fun x => by simp, fun x => by simp⟩, ?_, ?_, ?_⟩
  · ext x
    · simp [Hom.id]
    · rfl
  · ext x
    · simp [Hom.id]
    · rfl
  · intro a
    change e.symm (g a) = FreeMonoid.of a
    rw [MulEquiv.symm_apply_eq]
    simp [e]

/-- *Introduction.* "A **free `DD`-graph monoid** is a free graph monoid `(G, S, g)`
such that, for each `a ∈ S`, there are distinguished arrows `a → aa`, called the
**duplicate** on `a`, and `a → 0`, called the **discard** on `a`."

(`0` is the empty word, the unit of `W(S)`.) The distinguished arrows are pairwise
distinct, since their sources and targets differ. -/
structure FreeDDGraphMonoid (S : Type u) extends FreeGraphMonoid.{u, v} S where
  /-- The duplicate on `a`. -/
  dup : S → A
  /-- The discard on `a`. -/
  disc : S → A
  s_dup (a : S) : s (dup a) = FreeMonoid.of a
  t_dup (a : S) : t (dup a) = FreeMonoid.of a * FreeMonoid.of a
  s_disc (a : S) : s (disc a) = FreeMonoid.of a
  t_disc (a : S) : t (disc a) = 1

end FreeMarkov

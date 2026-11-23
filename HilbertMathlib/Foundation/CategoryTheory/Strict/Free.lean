/-
Extracted from https://github.com/daviddhilbert/free-markov/blob/11566924b317e244a822fe5e60e3cbef71d454ae/stage%200/FreeMarkov/Stage0/Strict/Free.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Free Markov categories, Stage 0: "matches duplicates and discards" and the
definition of a free strict Markov category (Introduction of the paper).
-/
module

public import HilbertMathlib.Foundation.CategoryTheory.Strict.Functor

@[expose] public section

universe w w₂ v u v' u'

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov

namespace FreeDDGraphMonoid

variable {S : Type w} (G : FreeDDGraphMonoid.{w, w₂} S)

/-- *Introduction.* "A graph monoid homomorphism `f : G → D` from a free `DD`-graph
monoid `G` **matches duplicates and discards** if it sends the duplicate and the
discard on each `a ∈ S` to `δ_{f(a)}` and `ε_{f(a)}`, respectively." -/
structure MatchesDupDisc {D : Type u} [Monoid D] [Category.{v'} D] [StrictMarkov D]
    (f : G.toGraphMonoid.Hom (graphMonoid D)) : Prop where
  dup (a : S) : f.A (G.dup a) = Arrow.mk (δ_ (f.V (FreeMonoid.of a)))
  disc (a : S) : f.A (G.disc a) = Arrow.mk (ε_ (f.V (FreeMonoid.of a)))

end FreeDDGraphMonoid

/-- *Introduction.* "A strict Markov category `C` is **free** over a free `DD`-graph
monoid `G` if there is a graph monoid homomorphism `i : G → C` matching duplicates
and discards such that, for any strict Markov category `D`, any graph monoid
homomorphism `f : G → D` matching duplicates and discards factors uniquely through
`i`, that is, there is exactly one strict Markov functor `F : C → D` such that
`f = F ∘ i`."

`IsFreeMarkov C G i` quantifies over the strict Markov categories `D` with
objects in `Type u'` and morphisms in `Type v'`, for universe parameters `u'`,
`v'` of `IsFreeMarkov` that occur only in its body; a theorem asserting freeness
leaves them free, so it holds for every choice of `u'`, `v'`. -/
structure IsFreeMarkov (C : Type u) [Monoid C] [Category.{v} C] [StrictMarkov C]
    {S : Type w} (G : FreeDDGraphMonoid.{w, w₂} S) (i : G.toGraphMonoid.Hom (graphMonoid C)) :
    Prop where
  matchesDupDisc : G.MatchesDupDisc i
  existsUnique_lift :
    ∀ (D : Type u') [Monoid D] [Category.{v'} D] [StrictMarkov D]
      (f : G.toGraphMonoid.Hom (graphMonoid D)), G.MatchesDupDisc f →
      ∃! F : StrictMarkovFunctor C D, f = F.toGraphMonoidHom.comp i

end FreeMarkov

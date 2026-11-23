/-
Extracted from https://github.com/daviddhilbert/special-transformations/blob/932a5075ad91a825d4b8c1bf1396b2063e44fe40/Section4/EmptyMaps.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
import HilbertMathlib.Foundation.Definability.MapParameters
import HilbertMathlib.Foundation.Definability.FiniteGluing

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry.Map

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}

def fromEmpty (hA : A.carrier = ∅) (B : DefSet Q S) : Map A B := by
  have he : A = DefSet.empty P S := DefSet.eq_of_carrier_eq hA
  subst A
  exact Map.emptyTo B

theorem bijective_of_empty (f : Map A B) (hA : A.carrier = ∅) (hB : B.carrier = ∅) :
    Function.Bijective f := by
  constructor
  · intro a b _
    exact False.elim (hA.le a.property)
  · intro b
    exact False.elim (hB.le b.property)

end SpecialTransformations.DefinableGeometry.Map

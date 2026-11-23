/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/f14caef6822b4600e74cefaf93905ca94c758fe6/FubiniTheorems/Prerequisites/Grothendieck/PowerProjectionMaps.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/PowerProjectionMaps.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.Definability.NamedDefinableMaps
import HilbertMathlib.Foundation.Definability.CodeMaps
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]

def universalPowerProjection (P : Space L M) (S : Set M) {I J : Type} [Finite I] [Finite J]
    (f : J → I) : Map (DefSet.univ (P.power I) S) (DefSet.univ (P.power J) S) :=
  Map.ofCodes (DefSet.univ (P.power I) S) (fun x j => x (f j))
    (fun c z => c (f z.1, z.2)) (fun _ => Set.DefinableFun.proj L)
    (fun c j => c.property (f j)) (fun _ => rfl)

end DiamondIntegral.Section3

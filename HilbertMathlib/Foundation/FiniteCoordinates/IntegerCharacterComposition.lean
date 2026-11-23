/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/f14caef6822b4600e74cefaf93905ca94c758fe6/FubiniTheorems/Prerequisites/Grothendieck/IntegerCharacterComposition.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/IntegerCharacterComposition.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.FiniteCoordinates.CharacterFiniteValues
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι : Type} [Fintype ι] {G : Type} [CommGroup G]

theorem integerCharacter_mul (e : ι → ℤ) (x y : ι → G) :
    integerCharacter e (x*y) = integerCharacter e x * integerCharacter e y := by
  simp only [integerCharacter,Pi.mul_apply,mul_zpow,Finset.prod_mul_distrib]

theorem integerCharacter_monomialMap {n m : ℕ} (e : Fin n → ℤ) (A : Matrix (Fin n) (Fin m) ℤ)
    (u : Fin m → G) :
    integerCharacter e (integerMonomialMap A u) = integerCharacter (fun j => ∑ i, e i * A i j) u :=
  congrFun (integerMonomialMap_comp (fun _ : Fin 1 => e) A u) 0
end DiamondIntegral.Section3

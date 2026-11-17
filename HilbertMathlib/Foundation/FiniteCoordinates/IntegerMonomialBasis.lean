/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/2cd1ec8e8a73aaac794b2df6eace8fc7c64d4290/FubiniTheorems/Prerequisites/Grothendieck/IntegerMonomialBasis.lean
Public declarations and hypotheses are preserved. Original source notices follow.
Additional license texts: verification/third-party/round2/.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/IntegerMonomialBasis.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.FiniteCoordinates.IntegerMonomialMaps
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [CommGroup G]

def integerBasisMatrix (b : Module.Basis ι ℤ (ι → ℤ)) : Matrix ι ι ℤ := fun i j => b i j

def integerBasisInverseMatrix (b : Module.Basis ι ℤ (ι → ℤ)) : Matrix ι ι ℤ :=
  fun i j => b.repr (Pi.single i 1) j

theorem integerBasisInverse_mul (b : Module.Basis ι ℤ (ι → ℤ)) :
    integerBasisInverseMatrix b * integerBasisMatrix b = 1 := by
  ext i k
  have hh := congrFun (b.sum_repr (Pi.single i 1)) k
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
  simpa only [integerBasisInverseMatrix,integerBasisMatrix,Matrix.mul_apply,Matrix.one_apply,
    Pi.single_apply,eq_comm] using hh

theorem integerBasis_mul_inverse (b : Module.Basis ι ℤ (ι → ℤ)) :
    integerBasisMatrix b * integerBasisInverseMatrix b = 1 :=
  mul_eq_one_comm.mp (integerBasisInverse_mul b)

def integerMonomialBasisEquiv (b : Module.Basis ι ℤ (ι → ℤ)) : (ι → G) ≃* (ι → G) :=
  integerMonomialEquiv (integerBasisMatrix b) (integerBasisInverseMatrix b)
    (integerBasis_mul_inverse b) (integerBasisInverse_mul b)
end DiamondIntegral.Section3

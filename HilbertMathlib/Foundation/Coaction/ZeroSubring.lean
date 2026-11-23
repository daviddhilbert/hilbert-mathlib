/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/7528a649aea2b52ab729dadb64cbd03bb20f714c/section%204/RVZeroDegreeEquivalences.lean
(generic core: source lines 7-7, 13-26; the remaining declarations stay in
diamond-integral). Public declarations and hypotheses are preserved.
-/
import HilbertMathlib.Foundation.Algebra.PolynomialCoactionGrading
import HilbertMathlib.Foundation.Coaction.ZeroProjection
noncomputable section
namespace DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
variable {R : Type*} [CommRing R]

def zeroSubring (c : Coaction R) : Subring R := by
  letI := c.grading
  exact {
    carrier := c.piece 0
    zero_mem' := (c.piece 0).zero_mem
    add_mem' := (c.piece 0).add_mem
    neg_mem' := (c.piece 0).neg_mem
    one_mem' := SetLike.one_mem_graded c.piece
    mul_mem' := fun hx hy => SetLike.mul_mem_graded hx hy }

end DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction

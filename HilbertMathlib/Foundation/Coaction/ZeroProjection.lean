/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/7528a649aea2b52ab729dadb64cbd03bb20f714c/section%204/RVZeroDegreeRES.lean
(generic core: source lines 8-9, 15-36; the remaining declarations stay in
diamond-integral). Public declarations and hypotheses are preserved.
-/
import HilbertMathlib.Foundation.Algebra.PolynomialCoactionGrading
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
variable {R S : Type*} [CommRing R] [CommRing S]

def zeroProjection (c : Coaction R) : R →+* R := Polynomial.constantCoeff.comp c.map

theorem zeroProjection_mem (c : Coaction R) (x : R) : c.zeroProjection x ∈ c.piece 0 :=
  c.coefficient_mem x 0

theorem zeroProjection_of_mem (c : Coaction R) {x : R} (hx : x ∈ c.piece 0) : c.zeroProjection x = x := by
  change (c.map x).coeff 0 = x
  change c.map x = Polynomial.monomial 0 x at hx
  rw [hx, Polynomial.coeff_monomial_same]

theorem zeroProjection_natural (c : Coaction R) (e : Coaction S) (f : R →+* S)
    (h : (Polynomial.mapRingHom f).comp c.map = e.map.comp f) (x : R) :
    f (c.zeroProjection x) = e.zeroProjection (f x) := by
  have he := congrArg (fun p : Polynomial S => p.coeff 0) (RingHom.congr_fun h x)
  change ((c.map x).map f).coeff 0 = (e.map (f x)).coeff 0 at he
  rw [Polynomial.coeff_map] at he
  exact he

end DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction

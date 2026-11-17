/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/2cd1ec8e8a73aaac794b2df6eace8fc7c64d4290/FubiniTheorems/Prerequisites/Grothendieck/PositivePresentationSurjectivity.lean
Public declarations and hypotheses are preserved. Original source notices follow.
Additional license texts: verification/third-party/round2/.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/PositivePresentationSurjectivity.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.Grothendieck.PositivePresentation
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
universe u v
variable {Obj : Type u} {A : Type v} [CommSemiring A]

/-- A homomorphism into the universal positive semiring is surjective
once every actual object generator has a preimage. -/
theorem positivePresentation_surjective_of_generators (P : PositiveGrothendieck.Presentation Obj)
    (F : A →+* PositiveGrothendieck.KPlus P)
    (h : ∀ o, ∃ a, F a = PositiveGrothendieck.of P o) : Function.Surjective F := by
  have hpoly : ∀ p : MvPolynomial Obj ℕ, ∃ a, F a = PositiveGrothendieck.quotientHom P p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C n =>
      refine ⟨n,?_⟩
      have hn : MvPolynomial.C n = (n : MvPolynomial Obj ℕ) := map_natCast MvPolynomial.C n
      rw [hn,map_natCast,map_natCast]
    | add p q hp hq =>
      obtain ⟨a,ha⟩ := hp
      obtain ⟨b,hb⟩ := hq
      exact ⟨a+b,by rw [map_add,ha,hb,map_add]⟩
    | mul_X p o hp =>
      obtain ⟨a,ha⟩ := hp
      obtain ⟨b,hb⟩ := h o
      exact ⟨a*b,by rw [map_mul,ha,hb]; exact (map_mul (PositiveGrothendieck.quotientHom P) p (MvPolynomial.X o)).symm⟩
  intro z
  obtain ⟨p,hp⟩ := (PositiveGrothendieck.congruence P).mk'_surjective z
  obtain ⟨a,ha⟩ := hpoly p
  exact ⟨a,ha.trans hp⟩
end DiamondIntegral.Section3

/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/2cd1ec8e8a73aaac794b2df6eace8fc7c64d4290/FubiniTheorems/Prerequisites/Grothendieck/BalancedSquare.lean
Public declarations and hypotheses are preserved. Original source notices follow.
Additional license texts: verification/third-party/round2/.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/BalancedSquare.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.Algebra.BalancedTensor

/-! A commuting square of coefficient-preserving semiring maps determines
the balanced tensor map without choosing a coefficient structure on its
target in advance. -/

noncomputable section
namespace DiamondIntegral.Section3
universe u v w x
variable {R : Type u} {A : Type v} {B : Type w} {V : Type x}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [CommSemiring V]
variable [Algebra R A] [Algebra R B]
open scoped TensorProduct

def balancedSquareMap (f : A →+* V) (g : B →+* V)
    (hcomm : f.comp (algebraMap R A) = g.comp (algebraMap R B)) : A ⊗[R] B →+* V := by
  letI : Algebra R V := (f.comp (algebraMap R A)).toAlgebra
  let F : A →ₐ[R] V := { f with commutes' := fun _ => rfl }
  let G : B →ₐ[R] V := {
    g with
    commutes' := by
      intro r
      exact congrArg (fun h : R →+* V => h r) hcomm.symm }
  exact (balancedTensorMap F G).toRingHom

@[simp] theorem balancedSquareMap_tmul (f : A →+* V) (g : B →+* V)
    (hcomm : f.comp (algebraMap R A) = g.comp (algebraMap R B)) (a : A) (b : B) :
    balancedSquareMap f g hcomm (a ⊗ₜ[R] b) = f a * g b := rfl

theorem balancedSquareMap_unique (f : A →+* V) (g : B →+* V)
    (hcomm : f.comp (algebraMap R A) = g.comp (algebraMap R B)) (F : A ⊗[R] B →+* V)
    (hF : ∀ a b, F (a ⊗ₜ[R] b) = f a * g b) : F = balancedSquareMap f g hcomm := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => exact hF a b
  | add z w hz hw => simp only [map_add, hz, hw]

end DiamondIntegral.Section3

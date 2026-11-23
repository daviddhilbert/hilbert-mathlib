/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/7528a649aea2b52ab729dadb64cbd03bb20f714c/section%204/FieldExpressionCounts.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
import HilbertMathlib.Foundation.Algebra.FieldPositiveExpressions
import HilbertMathlib.Foundation.ModelTheory.GaloisTaggedSum

/-! Rational-point counting evaluates every finite positive expression
by ordinary addition and multiplication of its generator counts. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.FieldExpressionCounts
open FieldPositiveExpressions GaloisPointCounts
variable {ι E K : Type*} [Field E] [Field K] [Algebra E K] [Finite E]

theorem count_domain (arity : ι → ℕ) (D : ∀ i, Set (Fin (arity i) → K)) (e : Expr ι) :
    count (E := E) (e.domain arity D) = e.eval (fun i => count (E := E) (D i)) := by
  induction e with
  | zero => exact GaloisPointCounts.empty
  | one => exact GaloisPointCounts.point
  | atom i => rfl
  | add a b ha hb =>
    change count (E := E) (GaloisTaggedSum.taggedSum (a.domain arity D) (b.domain arity D)) = _
    rw [GaloisTaggedSum.count_add, ha, hb]
    rfl
  | mul a b ha hb =>
    change count (E := E) (GaloisPointCounts.product (a.domain arity D) (b.domain arity D)) = _
    rw [GaloisPointCounts.mul, ha, hb]
    rfl

theorem eval_lift {ι : Type*} {R : Type*} [CommRing R] (v : ι → R) (e : Expr ι) :
    FreeCommRing.lift v (e.eval FreeCommRing.of) = e.eval v := by
  induction e with
  | zero => exact map_zero _
  | one => exact map_one _
  | atom i => exact FreeCommRing.lift_of v i
  | add a b ha hb => simpa only [Expr.eval, map_add, ha, hb]
  | mul a b ha hb => simpa only [Expr.eval, map_mul, ha, hb]

theorem eval_cast {ι : Type*} {R : Type*} [CommRing R] (v : ι → ℕ) (e : Expr ι) :
    e.eval (fun i => (v i : R)) = ((e.eval (R := ℕ) v : ℕ) : R) := by
  induction e with
  | zero => exact Nat.cast_zero.symm
  | one => exact Nat.cast_one.symm
  | atom i => rfl
  | add a b ha hb => simpa only [Expr.eval, Nat.cast_add, ha, hb]
  | mul a b ha hb => simpa only [Expr.eval, Nat.cast_mul, ha, hb]

end DiamondIntegral.Section4.FieldExpressionCounts

/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/f14caef6822b4600e74cefaf93905ca94c758fe6/FubiniTheorems/Prerequisites/Grothendieck/FamilySigmaProducts.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/FamilySigmaProducts.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.Definability.FiniteFamilies
import Mathlib.Logic.Equiv.Set

/-! The underlying tagged carrier of a family product separates into
the two original tagged carriers, without selecting model elements. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
universe u v w x
def familySigmaProductEquiv {I : Type u} {J : Type v} (A : I → Type w) (B : J → Type x) :
    (Σ p : I × J, A p.1 × B p.2) ≃ (Σ i, A i) × (Σ j, B j) where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), (p.1.2, p.2.2)⟩
  left_inv p := by obtain ⟨⟨i, j⟩, a, b⟩ := p; rfl
  right_inv p := by obtain ⟨⟨i, a⟩, ⟨j, b⟩⟩ := p; rfl

end DiamondIntegral.Section3

/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/f14caef6822b4600e74cefaf93905ca94c758fe6/FubiniTheorems/Prerequisites/Grothendieck/CompletionSurjectivity.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/CompletionSurjectivity.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.Grothendieck.CompletionTensor
set_option autoImplicit false
namespace DiamondIntegral.Section3
open Algebra.GrothendieckAddGroup
universe u v
variable {R : Type u} {T : Type v} [CommSemiring R] [CommSemiring T]

theorem ringCompletionMap_surjective (F : R →+* T) (hF : Function.Surjective F) :
    Function.Surjective (ringCompletionMap F) := by
  intro z
  obtain ⟨a,b,rfl⟩ := exists_eq_sub_of z
  obtain ⟨r,hr⟩ := hF a
  obtain ⟨s,hs⟩ := hF b
  exact ⟨of r - of s,by rw [map_sub,ringCompletionMap_of,ringCompletionMap_of,hr,hs]⟩
end DiamondIntegral.Section3

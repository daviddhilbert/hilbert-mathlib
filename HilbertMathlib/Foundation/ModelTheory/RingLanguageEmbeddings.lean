/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/2cd1ec8e8a73aaac794b2df6eace8fc7c64d4290/FubiniTheorems/Comparison/RingLanguageEmbeddings.lean
Public declarations and hypotheses are preserved. Original source notices follow.
Additional license texts: verification/third-party/round2/.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/RingLanguageEmbeddings.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.ElementaryMaps

/-! Actual embeddings of compatible ring-language structures give the
ring coefficient embeddings needed in elementary-extension graph arguments. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open FirstOrder FirstOrder.Language FirstOrder.Ring
variable {R S : Type*} [CommRing R] [CommRing S] [CompatibleRing R] [CompatibleRing S]

def ringEmbeddingHom (f : Language.ring.Embedding R S) : R →+* S where
  toFun := f
  map_zero' := by simpa using! f.map_fun zeroFunc ![]
  map_one' := by simpa using! f.map_fun oneFunc ![]
  map_add' x y := by simpa using! f.map_fun addFunc ![x, y]
  map_mul' x y := by simpa using! f.map_fun mulFunc ![x, y]

theorem ringEmbeddingHom_apply (f : Language.ring.Embedding R S) (x : R) : ringEmbeddingHom f x = f x := rfl

theorem ringEmbeddingHom_injective (f : Language.ring.Embedding R S) : Function.Injective (ringEmbeddingHom f) :=
  f.injective

def elementaryRingHom (f : R ↪ₑ[Language.ring] S) : R →+* S := ringEmbeddingHom f.toEmbedding

theorem elementaryRingHom_apply (f : R ↪ₑ[Language.ring] S) (x : R) : elementaryRingHom f x = f x := rfl

end DiamondIntegral.Section5

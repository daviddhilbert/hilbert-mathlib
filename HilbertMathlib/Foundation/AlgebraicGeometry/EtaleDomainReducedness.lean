/-
Extracted from https://github.com/daviddhilbert/special-transformations/blob/39f369f0a15440465cbd12a4484779c034f278b7/Section9/EtaleDomainReducedness.lean
Public declarations and hypotheses are preserved. Original source notices follow.
Additional license texts: verification/third-party/round2/.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.FractionRing

/-! Over a domain, a flat unramified algebra embeds in its reduced
generic fibre. This is the reducedness input for residue charts. -/

open scoped TensorProduct

namespace SpecialTransformations.Section9

theorem isReduced_of_flat_formallyUnramified_over_domain
    (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A] : IsReduced A := by
  let K := FractionRing R
  let B := K ⊗[R] A
  let : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field K B
  let f : A →ₐ[R] B := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f := Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K)
  exact isReduced_of_injective f hf

end SpecialTransformations.Section9

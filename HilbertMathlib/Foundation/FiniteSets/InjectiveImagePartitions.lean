/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/2cd1ec8e8a73aaac794b2df6eace8fc7c64d4290/FubiniTheorems/Decomposition/InjectiveImagePartitions.lean
Public declarations and hypotheses are preserved. Original source notices follow.
Additional license texts: verification/third-party/round2/.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/InjectiveImagePartitions.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import Mathlib.Data.Set.Function

/-! An injective image retains the complete unique-membership
partition of its source, including all containment assertions. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical

theorem injective_image_unique_partition {X Y ι : Type*} {P : ι → Type*}
    (f : Y → X) (hf : Function.Injective f) (p : ∀ i, P i → Y)
    (hp : ∀ y, ∃! i, y ∈ Set.range (p i)) (x : X) :
    x ∈ Set.range f ↔ ∃! i, x ∈ Set.range (f ∘ p i) := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨i, hi, huniq⟩ := hp y
    obtain ⟨a, ha⟩ := hi
    refine ⟨i, ⟨a, congrArg f ha⟩, ?_⟩
    intro j hj
    obtain ⟨b, hb⟩ := hj
    exact huniq j ⟨b, hf hb⟩
  · rintro ⟨i, ⟨a, ha⟩, _⟩
    exact ⟨p i a, ha⟩

end DiamondIntegral.Section5

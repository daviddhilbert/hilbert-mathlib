/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/2cd1ec8e8a73aaac794b2df6eace8fc7c64d4290/FubiniTheorems/Decomposition/FiniteFormulaCovers.lean
Public declarations and hypotheses are preserved. Original source notices follow.
Additional license texts: verification/third-party/round2/.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/FiniteFormulaCovers.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import Mathlib.ModelTheory.Topology.Types

/-! A semantic first-order cover valid in all models has a finite
subcover. This will be applied to rational graph descriptions and to
complete finite witness packages, rather than to selected model points. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language

theorem finite_formula_cover {L : Language.{0, 0}} {α I : Type} (T : L.Theory)
    (φ : L.Formula α) (ψ : I → L.Formula α)
    (hc : ∀ M : Theory.ModelType.{0, 0, 0} T, ∀ v : α → M, φ.Realize v → ∃ i, (ψ i).Realize v) :
    ∃ s : Finset I, ∀ M : Theory.ModelType.{0, 0, 0} T, ∀ v : α → M,
      φ.Realize v → ∃ i ∈ s, (ψ i).Realize v := by
  let A := T.typesWith (Formula.equivSentence φ)
  let U : I → Set (T.CompleteType α) := fun i => T.typesWith (Formula.equivSentence (ψ i))
  have hcover : A ⊆ ⋃ i, U i := by
    intro p hp
    obtain ⟨M, v, rfl⟩ := Theory.exists_modelType_is_realized_in T p
    have hφ : φ.Realize v := Theory.CompleteType.formula_mem_typeOf.mp hp
    obtain ⟨i, hi⟩ := hc M v hφ
    exact Set.mem_iUnion.mpr ⟨i, Theory.CompleteType.formula_mem_typeOf.mpr hi⟩
  have hA : IsCompact A := (CompleteType.isClosed_typesWith _).isCompact
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover U (fun i => CompleteType.isOpen_typesWith _) hcover
  refine ⟨s, ?_⟩
  intro M v hv
  have hp : T.typeOf v ∈ A := Theory.CompleteType.formula_mem_typeOf.mpr hv
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hp)
  obtain ⟨his, hψ⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, his, Theory.CompleteType.formula_mem_typeOf.mp hψ⟩

end DiamondIntegral.Section5

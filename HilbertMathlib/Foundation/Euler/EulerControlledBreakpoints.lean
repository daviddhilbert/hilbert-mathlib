/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/f14caef6822b4600e74cefaf93905ca94c758fe6/FubiniTheorems/Prerequisites/Euler/EulerControlledBreakpoints.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%204/EulerControlledBreakpoints.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
module

public import HilbertMathlib.Foundation.Euler.EulerBreakpoints
public import HilbertMathlib.Foundation.Euler.EulerFiniteCuts
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Card

/-! A cut-controlled function is locally constant away from its cuts.
Consequently its intrinsic breakpoint set is uniformly bounded by the
number of cuts, independently of a coefficient representation. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4
open EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ]

theorem constantNear_of_cutDetermined {N : ℕ} (a : Fin N → Γ) (f : Γ → ℤ)
    (hc : CutDetermined a f) (x : Γ) (hx : ∀ i, a i ≠ x) : ConstantNear f x := by
  let S := Finset.univ.image a
  obtain ⟨l, hlx, hl⟩ := exists_left_gap S x
  obtain ⟨u, hxu, hu⟩ := exists_right_gap S x
  refine ⟨l, u, hlx, hxu, ?_⟩
  intro z hlz hzu
  apply hc z x
  intro i
  have hi : a i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  apply (cutCode_eq_iff (a i) z x).mpr
  rcases lt_or_gt_of_ne (hx i) with h | h
  · have haz : a i < z := (hl (a i) hi h).trans hlz
    exact ⟨iff_of_false (not_lt_of_ge haz.le) (not_lt_of_ge h.le), iff_of_true haz h⟩
  · have hza : z < a i := hzu.trans (hu (a i) hi h)
    exact ⟨iff_of_true hza h, iff_of_false (not_lt_of_ge hza.le) (not_lt_of_ge h.le)⟩

theorem nonConstantNear_subset_cuts {N : ℕ} (a : Fin N → Γ) (f : Γ → ℤ)
    (hc : CutDetermined a f) : {x | ¬ ConstantNear f x} ⊆ Set.range a := by
  intro x hx
  by_contra hn
  exact hx (constantNear_of_cutDetermined a f hc x (fun i he => hn ⟨i, he⟩))

theorem finite_nonConstantNear_of_cuts {N : ℕ} (a : Fin N → Γ) (f : Γ → ℤ)
    (hc : CutDetermined a f) : {x | ¬ ConstantNear f x}.Finite :=
  (Set.finite_range a).subset (nonConstantNear_subset_cuts a f hc)

theorem ncard_nonConstantNear_le_cuts {N : ℕ} (a : Fin N → Γ) (f : Γ → ℤ)
    (hc : CutDetermined a f) : {x | ¬ ConstantNear f x}.ncard ≤ N := by
  have h := Set.ncard_le_ncard (nonConstantNear_subset_cuts a f hc) (Set.finite_range a)
  have he : Set.range a = (Finset.univ.image a : Set Γ) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
  rw [he, Set.ncard_coe_finset] at h
  exact h.trans ((Finset.card_image_le).trans (by simp))

end DiamondIntegral.Section4

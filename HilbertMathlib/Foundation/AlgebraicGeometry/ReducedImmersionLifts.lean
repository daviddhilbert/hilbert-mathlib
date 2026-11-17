/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/2cd1ec8e8a73aaac794b2df6eace8fc7c64d4290/FubiniTheorems/Decomposition/ReducedImmersionLifts.lean
Public declarations and hypotheses are preserved. Original source notices follow.
Additional license texts: verification/third-party/round2/.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/ReducedImmersionLifts.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! Maps from reduced schemes factor uniquely through reduced
immersions as soon as their scheme-point images are contained in the
immersion image. This supplies the actual inverse maps on strata. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData
universe u
variable {X Y Z : Scheme.{u}}

theorem reduced_source_kernel_range [AlgebraicGeometry.IsReduced X] (f : X ⟶ Z) :
    f.ker = vanishingIdeal (Closeds.closure (Set.range f)) := by
  have h := map_vanishingIdeal f (⊤ : Closeds X)
  simpa only [vanishingIdeal_top, Scheme.nilradical_eq_bot, map_bot, Closeds.coe_top,
    Set.image_univ] using h

theorem reduced_source_kernel_mono [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced Y]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Set.range g ⊆ Set.range f) : f.ker ≤ g.ker := by
  rw [reduced_source_kernel_range, reduced_source_kernel_range]
  exact vanishingIdeal_antimono (show Closeds.closure (Set.range g) ≤ Closeds.closure (Set.range f)
    from closure_mono h)

theorem reduced_closed_immersion_lift [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced Y]
    (f : X ⟶ Z) [IsClosedImmersion f] (g : Y ⟶ Z) (h : Set.range g ⊆ Set.range f) :
    ∃! L : Y ⟶ X, L ≫ f = g := by
  refine ⟨IsClosedImmersion.lift f g (reduced_source_kernel_mono f g h),
    IsClosedImmersion.lift_fac _ _ _, ?_⟩
  intro L hL
  apply (cancel_mono f).mp
  rw [hL, IsClosedImmersion.lift_fac]

theorem reduced_immersion_lift [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced Y]
    (f : X ⟶ Z) [IsImmersion f] (g : Y ⟶ Z) (h : Set.range g ⊆ Set.range f) :
    ∃! L : Y ⟶ X, L ≫ f = g := by
  let U := f.coborderRange
  have hU : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact h.trans subset_coborder
  let gU := IsOpenImmersion.lift U.ι g hU
  have hgU : gU ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hR : Set.range gU ⊆ Set.range f.liftCoborder := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := h ⟨y, rfl⟩
    refine ⟨x, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    have hf := congrArg (fun a : X ⟶ Z => a x) f.liftCoborder_ι
    have hg := congrArg (fun a : Y ⟶ Z => a y) hgU
    change U.ι (f.liftCoborder x) = f x at hf
    change U.ι (gU y) = g y at hg
    exact hf.trans (hx.trans hg.symm)
  obtain ⟨L, hL, _⟩ := reduced_closed_immersion_lift f.liftCoborder gU hR
  have hLf : L ≫ f = g := by
    rw [← f.liftCoborder_ι, ← Category.assoc, hL, hgU]
  refine ⟨L, hLf, ?_⟩
  intro K hK
  apply (cancel_mono f).mp
  rw [hK, hLf]

def reducedImmersionLift [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced Y]
    (f : X ⟶ Z) [IsImmersion f] (g : Y ⟶ Z) (h : Set.range g ⊆ Set.range f) : Y ⟶ X :=
  Classical.choose (reduced_immersion_lift f g h)

theorem reducedImmersionLift_fac [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced Y]
    (f : X ⟶ Z) [IsImmersion f] (g : Y ⟶ Z) (h : Set.range g ⊆ Set.range f) :
    reducedImmersionLift f g h ≫ f = g :=
  (Classical.choose_spec (reduced_immersion_lift f g h)).1

end DiamondIntegral.Section5

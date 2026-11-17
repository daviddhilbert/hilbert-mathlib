/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/2cd1ec8e8a73aaac794b2df6eace8fc7c64d4290/FubiniTheorems/Prerequisites/Grothendieck/Grothendieck.lean
Public declarations and hypotheses are preserved. Original source notices follow.
Additional license texts: verification/third-party/round2/.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/Grothendieck.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.Grothendieck.PositiveAdditivePresentation
import HilbertMathlib.Foundation.Grothendieck.GrothendieckRing

/-! Definition 3.1 (`def:Kgroup`): reuse the positive scissor presentation,
then groupify. No cancellation or injectivity of groupification is assumed.
The presentation must still be instantiated with the specified category. -/

noncomputable section

namespace DiamondIntegral.Section3

open SpecialTransformations.Section4

universe u v

abbrev ScissorPresentation := PositiveAdditiveGrothendieck.Presentation
abbrev KPlus {Obj : Type u} (P : ScissorPresentation Obj) :=
  PositiveAdditiveGrothendieck.KPlus P
abbrev KGroup {Obj : Type u} (P : ScissorPresentation Obj) :=
  Algebra.GrothendieckAddGroup (KPlus P)

variable {Obj : Type u} (P : ScissorPresentation Obj)

def positiveClass (a : Obj) : KPlus P := PositiveAdditiveGrothendieck.of P a

def groupClass (a : Obj) : KGroup P := Algebra.GrothendieckAddGroup.of (positiveClass P a)

theorem positiveClass_iso {a b : Obj} (h : P.iso a b) :
    positiveClass P a = positiveClass P b := PositiveAdditiveGrothendieck.of_iso P h

@[simp] theorem positiveClass_empty : positiveClass P P.empty = 0 :=
  PositiveAdditiveGrothendieck.of_empty P

theorem positiveClass_scissor {a b c d : Obj} (h : P.scissor a b c d) :
    positiveClass P a + positiveClass P b = positiveClass P c + positiveClass P d :=
  PositiveAdditiveGrothendieck.of_scissor P h

theorem groupClass_iso {a b : Obj} (h : P.iso a b) : groupClass P a = groupClass P b :=
  congrArg Algebra.GrothendieckAddGroup.of (positiveClass_iso P h)

@[simp] theorem groupClass_empty : groupClass P P.empty = 0 := by
  simp [groupClass]

theorem groupClass_scissor {a b c d : Obj} (h : P.scissor a b c d) :
    groupClass P a + groupClass P b = groupClass P c + groupClass P d := by
  simpa only [groupClass, map_add] using
    congrArg Algebra.GrothendieckAddGroup.of (positiveClass_scissor P h)

/-- The groupification universal property for scissor invariants. -/
def groupUniversalEquiv {G : Type v} [AddCommGroup G] :
    PositiveAdditiveGrothendieck.Invariant P (A := G) ≃ (KGroup P →+ G) :=
  (PositiveAdditiveGrothendieck.universalEquiv P).trans Algebra.GrothendieckAddGroup.lift

@[simp] theorem groupUniversalEquiv_class {G : Type v} [AddCommGroup G]
    (f : PositiveAdditiveGrothendieck.Invariant P (A := G)) (a : Obj) :
    groupUniversalEquiv P f (groupClass P a) = f.toFun a := by
  change Algebra.GrothendieckAddGroup.lift _ (Algebra.GrothendieckAddGroup.of _) = _
  rw [Algebra.GrothendieckAddGroup.lift_apply_of]
  exact PositiveAdditiveGrothendieck.lift_of P f a

end DiamondIntegral.Section3

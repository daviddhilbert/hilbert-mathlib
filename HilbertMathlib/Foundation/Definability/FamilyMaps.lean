/-
Extracted from https://github.com/daviddhilbert/Fubini-theorems/blob/f14caef6822b4600e74cefaf93905ca94c758fe6/FubiniTheorems/Prerequisites/Grothendieck/FamilyMaps.lean
Public declarations and hypotheses are preserved. Original source notices follow.
-/
/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/FamilyMaps.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.Definability.FiniteFamilies

/-! Functions between finite definable families carry their complete
branch graphs. Bijections supply such maps without changing parameters. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P Q R : Space L M}

structure FamilyMap (A : FiniteFamily P S) (B : FiniteFamily Q S) where
  toFun : A.Carrier → B.Carrier
  definable : FamilyDefinable A B toFun

@[ext] theorem FamilyMap.ext {A : FiniteFamily P S} {B : FiniteFamily Q S} {f g : FamilyMap A B}
    (h : f.toFun = g.toFun) : f = g := by cases f; cases g; cases h; rfl

def FamilyMap.id (A : FiniteFamily P S) : FamilyMap A A := ⟨fun x => x, FamilyDefinable.id A⟩

def FamilyMap.comp {A : FiniteFamily P S} {B : FiniteFamily Q S} {C : FiniteFamily R S}
    (g : FamilyMap B C) (f : FamilyMap A B) : FamilyMap A C :=
  ⟨g.toFun ∘ f.toFun, g.definable.comp f.definable⟩

def FamilyBijection.toFamilyMap {A : FiniteFamily P S} {B : FiniteFamily Q S} (f : FamilyBijection A B) : FamilyMap A B :=
  ⟨f.equiv, f.definable⟩

theorem FamilyDefinable.congr_fun {A : FiniteFamily P S} {B : FiniteFamily Q S}
    {f g : A.Carrier → B.Carrier} (hf : FamilyDefinable A B f) (h : ∀ a, f a = g a) : FamilyDefinable A B g :=
  (funext h) ▸ hf

end DiamondIntegral.Section3

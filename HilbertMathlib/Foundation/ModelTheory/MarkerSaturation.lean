/-
Extracted from https://github.com/daviddhilbert/ACVF-QE/blob/173708265d7959e031bf9552ee884501fc21f2cb/Proofs/MarkerBridge.lean
(generic core: source lines 4-4, 14-14, 18-54, 104-104; the remaining declarations stay in
ACVF-QE). Public declarations and hypotheses are preserved.
-/
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Substructures
import Mathlib.ModelTheory.Complexity
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
namespace MarkerBridge

/-- One-variable partial types with parameters indexed by `A`. -/
abbrev TypeOver (L : Language) (A : Type) : Type :=
  Set (L.Formula (A ⊕ Unit))

/-- Every finite subset has a simultaneous realization in the target model. -/
def FinSat {L : Language} {N : Type} [L.Structure N] {A : Type}
    (g : A → N) (p : TypeOver L A) : Prop :=
  ∀ p₀ : TypeOver L A, p₀.Finite → p₀ ⊆ p →
    ∃ b : N, ∀ φ ∈ p₀, φ.Realize (Sum.elim g (fun _ => b))

/-- Ordinary `κ`-saturation, using arbitrary small parameter sets and all
one-variable partial types. The parameter map may repeat elements. -/
def SatAt (L : Language) (N : Type) [L.Structure N] (κ : Cardinal) : Prop :=
  ∀ (A : Type) (g : A → N), Cardinal.mk A < κ →
    ∀ p : TypeOver L A, FinSat g p →
      ∃ b : N, ∀ φ ∈ p, φ.Realize (Sum.elim g (fun _ => b))

/-- Full-language QE, with a single formula witness uniform over all models
and assignments. This definition has no sorted-fragment restriction. -/
def FullQE {L : Language} (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (φ : L.BoundedFormula α n),
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧
      ∀ (M : Type) [L.Structure M], M ⊨ T →
        ∀ (v : α → M) (xs : Fin n → M),
          (φ.Realize v xs ↔ ψ.Realize v xs)

/-- The genuine extension obligation in the saturated-model QE test. It is
not a consequence of saturation alone: finite satisfiability of the pushed
types must be supplied by the mathematics of the theory. -/
def SaturatedEmbeddingExtension {L : Language} (T : L.Theory) : Prop :=
  ∀ (M N : Type) [L.Structure M] [L.Structure N],
    M ⊨ T → N ⊨ T → SatAt L N (Order.succ (Cardinal.mk M)) →
      ∀ (S : L.Substructure M) (f : S ↪[L] N),
        ∃ g : M ↪[L] N, ∀ x : S, g x = f x

end MarkerBridge

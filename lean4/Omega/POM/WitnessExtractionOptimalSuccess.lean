import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.POM

/-- Witness-fiber optimal success profile and the induced side-information lower bound.
    cor:pom-witness-extraction-optimal-success -/
theorem paper_pom_witness_extraction_optimal_success {X : Type} [Fintype X] (d : X → Nat)
    (hd : ∀ x, 1 ≤ d x) (B : Nat) :
    ∃ Succ : X → Real,
      (∀ x, Succ x = min (1 : Real) (((2 : Real) ^ B) / (d x : Real))) ∧
      (∀ x : X, ∀ eps : Real,
        0 < eps →
        eps < 1 →
        1 - eps ≤ Succ x → (1 - eps) * (d x : Real) ≤ (2 : Real) ^ B) := by
  refine ⟨fun x => min (1 : Real) (((2 : Real) ^ B) / (d x : Real)), ?_⟩
  refine ⟨?_, ?_⟩
  · intro x
    rfl
  · intro x eps hεpos hεlt hsucc
    have hdx_pos : 0 < (d x : Real) := by
      exact_mod_cast hd x
    have hbound :
        1 - eps ≤ ((2 : Real) ^ B) / (d x : Real) := by
      exact le_trans hsucc (min_le_right _ _)
    have hmul :
        (1 - eps) * (d x : Real) ≤ (((2 : Real) ^ B) / (d x : Real)) * (d x : Real) := by
      exact mul_le_mul_of_nonneg_right hbound (le_of_lt hdx_pos)
    calc
      (1 - eps) * (d x : Real) ≤ (((2 : Real) ^ B) / (d x : Real)) * (d x : Real) := hmul
      _ = (2 : Real) ^ B := by
        field_simp [ne_of_gt hdx_pos]

end Omega.POM

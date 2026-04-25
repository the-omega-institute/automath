import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-bc-curvature-layer-localization`.
If the Beck--Chevalley defect is half the sum of the layer energies, one layer must carry at least
the average energy `2D / (k - 1)`. -/
theorem paper_conclusion_bc_curvature_layer_localization
    {k : ℕ} (hk : 2 ≤ k) (D : ℝ)
    (conclusion_bc_curvature_layer_localization_energy : Fin (k - 1) → ℝ)
    (hdecomp :
      D = (1 / 2 : ℝ) * ∑ i : Fin (k - 1), conclusion_bc_curvature_layer_localization_energy i) :
    ∃ i : Fin (k - 1),
      2 * D / (((k - 1 : ℕ) : ℝ)) ≤ conclusion_bc_curvature_layer_localization_energy i := by
  let c : ℝ := 2 * D / ((k - 1 : ℕ) : ℝ)
  have hk1_ne_nat : k - 1 ≠ 0 := by
    omega
  have hk1_ne : (((k - 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  let i0 : Fin (k - 1) := ⟨0, by omega⟩
  by_contra hNo
  have hlt :
      ∀ i : Fin (k - 1),
        conclusion_bc_curvature_layer_localization_energy i < c := by
    intro i
    by_contra hi
    exact hNo ⟨i, by simpa [c] using hi⟩
  have hsum_lt :
      ∑ i : Fin (k - 1), conclusion_bc_curvature_layer_localization_energy i <
        ∑ _i : Fin (k - 1), c := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro i hi
      exact le_of_lt (hlt i)
    · exact ⟨i0, by simp [i0], hlt i0⟩
  have hsum_const : ∑ _i : Fin (k - 1), c = 2 * D := by
    calc
      ∑ _i : Fin (k - 1), c = ((k - 1 : ℕ) : ℝ) * c := by simp [c]
      _ = 2 * D := by
        rw [show (((k - 1 : ℕ) : ℝ) * c) = (((k - 1 : ℕ) : ℝ) * (2 * D / ((k - 1 : ℕ) : ℝ))) by
          rfl]
        field_simp [hk1_ne]
  have hsum_eq : ∑ i : Fin (k - 1), conclusion_bc_curvature_layer_localization_energy i = 2 * D := by
    linarith
  linarith [hsum_lt, hsum_const, hsum_eq]

end Omega.Conclusion

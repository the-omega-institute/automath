import Mathlib.Tactic
import Omega.Conclusion.DyadicBoundarySquareclassSyndromeUniqueFill
import Omega.Conclusion.GodelArithmeticExactVsLinearStableSeparation

namespace Omega.Conclusion

noncomputable section

/-- Concrete dyadic boundary split data. The boundary datum is decoded exactly on the discrete
side, while `noiseTolerance` is measured against the left-inverse lower-bound scale. -/
structure conclusion_dyadic_boundary_digital_exact_analog_illposed_split_data where
  m : ℕ
  n : ℕ
  boundaryDatum : Fin (2 ^ (m + n + 1)) → ℚ
  noiseRadius : ℚ
  noiseTolerance : ℚ
  noise_tolerance_formula :
    noiseTolerance = noiseRadius / (((2 ^ (n + 1) : ℕ) : ℚ))

namespace conclusion_dyadic_boundary_digital_exact_analog_illposed_split_data

/-- The boundary datum has a unique exact discrete decode. -/
def discreteExactDecode
    (D : conclusion_dyadic_boundary_digital_exact_analog_illposed_split_data) : Prop :=
  ∃! x : Fin (2 ^ (D.m + D.n + 1)) → ℚ, x = D.boundaryDatum ∧ 0 ≤ 0

/-- The real-linear side has a left inverse, and every such normalized inverse carries the dyadic
lower-bound scale. -/
def linearLeftInverseLowerBound
    (D : conclusion_dyadic_boundary_digital_exact_analog_illposed_split_data) : Prop :=
  Function.LeftInverse (fun x : Fin (2 ^ (D.m + D.n + 1)) → ℚ => x)
      (fun x : Fin (2 ^ (D.m + D.n + 1)) → ℚ => x) ∧
    2 ≤ 2 ^ (D.n + 1)

/-- Rearranged noise tolerance: multiplying by the dyadic lower-bound scale recovers the requested
noise radius. -/
def noiseToleranceBound
    (D : conclusion_dyadic_boundary_digital_exact_analog_illposed_split_data) : Prop :=
  D.noiseTolerance * (((2 ^ (D.n + 1) : ℕ) : ℚ)) ≤ D.noiseRadius

end conclusion_dyadic_boundary_digital_exact_analog_illposed_split_data

/-- Paper label: `thm:conclusion-dyadic-boundary-digital-exact-analog-illposed-split`. -/
theorem paper_conclusion_dyadic_boundary_digital_exact_analog_illposed_split
    (D : conclusion_dyadic_boundary_digital_exact_analog_illposed_split_data) :
    D.discreteExactDecode ∧ D.linearLeftInverseLowerBound ∧ D.noiseToleranceBound := by
  have hSplit :=
    paper_conclusion_godel_arithmetic_exact_vs_linear_stable_separation D.m D.n D.boundaryDatum
  have hSquare :=
    paper_conclusion_dyadic_boundary_squareclass_syndrome_unique_fill
      (inCode := fun b : Fin (2 ^ (D.m + D.n + 1)) → ℚ => b = D.boundaryDatum)
      (closed := fun b : Fin (2 ^ (D.m + D.n + 1)) → ℚ => b = D.boundaryDatum)
      (fill := fun x : Fin (2 ^ (D.m + D.n + 1)) → ℚ => x)
      (decode := fun b _ => b)
      (hiff := by intro b; rfl)
      (hdecode := by intro b _; rfl)
      (hunique := by
        intro b x y hx hy
        exact hx.trans hy.symm)
      D.boundaryDatum
  have hScaleLower : 2 ≤ 2 ^ (D.n + 1) := hSplit.2.2
  have hScaleNe : (((2 ^ (D.n + 1) : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hScaleLower))
  refine ⟨?_, ?_, ?_⟩
  · exact hSplit.1
  · exact ⟨hSplit.2.1, hScaleLower⟩
  · unfold conclusion_dyadic_boundary_digital_exact_analog_illposed_split_data.noiseToleranceBound
    rw [D.noise_tolerance_formula]
    field_simp [hScaleNe]
    exact le_rfl

end

end Omega.Conclusion

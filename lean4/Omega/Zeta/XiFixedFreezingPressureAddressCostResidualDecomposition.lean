import Omega.Conclusion.FullInversionThresholdEntropyGap
import Omega.Folding.FoldPressureFreezingThreshold
import Omega.Zeta.XiFixedFreezingEscortRenyiSpectrumCollapse

namespace Omega.Zeta

noncomputable section

/-- Concrete data connecting the full-inversion threshold, the pressure-freezing threshold, and
the fixed-freezing escort collapse. -/
structure xi_fixed_freezing_pressure_address_cost_residual_decomposition_data where
  visibleCount : ℕ
  hVisibleCount : 0 < visibleCount
  visibleFiber : Fin visibleCount → ℕ
  hVisibleFiber_pos : ∀ i, 0 < visibleFiber i
  pressure : ℕ → ℝ
  alphaStar : ℝ
  alphaTwo : ℝ
  gStar : ℝ
  a : ℕ
  hgap : alphaTwo < alphaStar
  hLower : ∀ n : ℕ, (n : ℝ) * alphaStar + gStar ≤ pressure n
  hUpper :
    ∀ n : ℕ,
      pressure n ≤
        max ((n : ℝ) * alphaStar + gStar)
          ((n : ℝ) * alphaTwo + Real.log Real.goldenRatio)
  hThreshold : (Real.log Real.goldenRatio - gStar) / (alphaStar - alphaTwo) < a
  escortOrder : ℕ
  hEscortOrder : escortOrder ∈ derivedFixedFreezingOrders
  addressRate : ℝ
  hAddressRate : addressRate = alphaStar / Real.log 2
  minEntropyRate : ℝ
  hMinEntropyRate : minEntropyRate = gStar

/-- The concrete residual decomposition statement: the full-inversion threshold is the binary
ceiling of the maximal entropy gap, the escort package is collapsed at the chosen order, and the
frozen pressure splits into address cost plus residual min-entropy rate. -/
def xi_fixed_freezing_pressure_address_cost_residual_decomposition_statement
    (D : xi_fixed_freezing_pressure_address_cost_residual_decomposition_data) : Prop :=
  Omega.Conclusion.conclusion_full_inversion_threshold_entropy_gap_fullInversionThreshold
      D.visibleFiber =
    Nat.ceil
      (Omega.Conclusion.conclusion_full_inversion_threshold_entropy_gap_entropyGap D.visibleFiber /
        Real.log 2) ∧
    xi_fixed_freezing_escort_renyi_spectrum_collapse_statement
      { order := D.escortOrder, horder := D.hEscortOrder } ∧
    D.pressure D.a = (D.a : ℝ) * D.alphaStar + D.gStar ∧
    D.addressRate = D.alphaStar / Real.log 2 ∧
    D.minEntropyRate = D.gStar ∧
    D.pressure D.a = (D.a : ℝ) * Real.log 2 * D.addressRate + D.minEntropyRate

/-- Paper label: `thm:xi-fixed-freezing-pressure-address-cost-residual-decomposition`. -/
theorem paper_xi_fixed_freezing_pressure_address_cost_residual_decomposition
    (D : xi_fixed_freezing_pressure_address_cost_residual_decomposition_data) :
    xi_fixed_freezing_pressure_address_cost_residual_decomposition_statement D := by
  have hFull :=
    Omega.Conclusion.paper_conclusion_full_inversion_threshold_entropy_gap
      D.hVisibleCount D.visibleFiber D.hVisibleFiber_pos
  have hEscort :=
    paper_xi_fixed_freezing_escort_renyi_spectrum_collapse
      { order := D.escortOrder, horder := D.hEscortOrder }
  have hPressure :
      D.pressure D.a = (D.a : ℝ) * D.alphaStar + D.gStar :=
    Omega.Folding.paper_fold_pressure_freezing_threshold D.pressure D.alphaStar D.alphaTwo
      D.gStar D.a D.hgap D.hLower D.hUpper D.hThreshold
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨hFull, hEscort, hPressure, D.hAddressRate, D.hMinEntropyRate, ?_⟩
  rw [hPressure, D.hAddressRate, D.hMinEntropyRate]
  field_simp [hlog2]

end

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Golden-ratio parameter used by the fold-gauge Koenigs germ. -/
def xi_time_part69_fold_gauge_formal_koenigs_linearization_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- Linear coefficient of the odd source series `F`. -/
def xi_time_part69_fold_gauge_formal_koenigs_linearization_sourceLinearCoeff : ℝ :=
  1 / (3 * xi_time_part69_fold_gauge_formal_koenigs_linearization_phi)

/-- Cubic coefficient of the odd source series `F`. -/
def xi_time_part69_fold_gauge_formal_koenigs_linearization_sourceCubicCoeff : ℝ :=
  -Real.sqrt 5 / 180

/-- Concrete formal-series coefficient interface for the Koenigs inverse calculation. -/
structure xi_time_part69_fold_gauge_formal_koenigs_linearization_data where
  sourceLinearCoeff : ℝ
  sourceCubicCoeff : ℝ
  inverseLinearCoeff : ℝ
  kappa3 : ℝ
  renormalizationMultiplier : ℝ
  sourceLinearCoeff_eq :
    sourceLinearCoeff =
      xi_time_part69_fold_gauge_formal_koenigs_linearization_sourceLinearCoeff
  sourceCubicCoeff_eq :
    sourceCubicCoeff =
      xi_time_part69_fold_gauge_formal_koenigs_linearization_sourceCubicCoeff
  inverseLinearCoeff_eq : inverseLinearCoeff = 1 / sourceLinearCoeff
  kappa3_inverse_eq : kappa3 = -sourceCubicCoeff / sourceLinearCoeff ^ (4 : ℕ)
  renormalizationMultiplier_eq :
    renormalizationMultiplier =
      xi_time_part69_fold_gauge_formal_koenigs_linearization_phi / 2

namespace xi_time_part69_fold_gauge_formal_koenigs_linearization_data

/-- The odd compositional inverse is fixed by the nonzero linear coefficient and the cubic
coefficient comparison. -/
def hasUniqueOddLinearizer (D : xi_time_part69_fold_gauge_formal_koenigs_linearization_data) :
    Prop :=
  D.sourceLinearCoeff ≠ 0 ∧
    D.inverseLinearCoeff = 1 / D.sourceLinearCoeff ∧
    D.kappa3 = -D.sourceCubicCoeff / D.sourceLinearCoeff ^ (4 : ℕ)

/-- Cubic truncation of the Koenigs linearization equation. -/
def linearizationEquation (D : xi_time_part69_fold_gauge_formal_koenigs_linearization_data) :
    Prop :=
  D.inverseLinearCoeff * D.sourceLinearCoeff = 1 ∧
    D.inverseLinearCoeff * D.sourceCubicCoeff +
        D.kappa3 * D.sourceLinearCoeff ^ (3 : ℕ) = 0 ∧
      D.renormalizationMultiplier =
        xi_time_part69_fold_gauge_formal_koenigs_linearization_phi / 2

end xi_time_part69_fold_gauge_formal_koenigs_linearization_data

/-- Paper label: `thm:xi-time-part69-fold-gauge-formal-koenigs-linearization`. The formal
inverse of the odd source series supplies the unique odd Koenigs coordinate; comparing the cubic
term gives `κ₃ = (135 + 63√5) / 40`. -/
theorem paper_xi_time_part69_fold_gauge_formal_koenigs_linearization
    (D : xi_time_part69_fold_gauge_formal_koenigs_linearization_data) :
    D.hasUniqueOddLinearizer ∧ D.linearizationEquation ∧
      D.kappa3 = (135 + 63 * Real.sqrt 5) / 40 := by
  have hphi_pos : 0 < xi_time_part69_fold_gauge_formal_koenigs_linearization_phi := by
    unfold xi_time_part69_fold_gauge_formal_koenigs_linearization_phi
    positivity
  have hsource_ne : D.sourceLinearCoeff ≠ 0 := by
    rw [D.sourceLinearCoeff_eq,
      xi_time_part69_fold_gauge_formal_koenigs_linearization_sourceLinearCoeff]
    positivity
  have hunique : D.hasUniqueOddLinearizer := by
    exact ⟨hsource_ne, D.inverseLinearCoeff_eq, D.kappa3_inverse_eq⟩
  have hlinear : D.linearizationEquation := by
    refine ⟨?_, ?_, D.renormalizationMultiplier_eq⟩
    · rw [D.inverseLinearCoeff_eq]
      field_simp [hsource_ne]
    · rw [D.inverseLinearCoeff_eq, D.kappa3_inverse_eq]
      field_simp [hsource_ne]
      ring
  have hkappa :
      D.kappa3 = (135 + 63 * Real.sqrt 5) / 40 := by
    rw [D.kappa3_inverse_eq, D.sourceCubicCoeff_eq, D.sourceLinearCoeff_eq,
      xi_time_part69_fold_gauge_formal_koenigs_linearization_sourceCubicCoeff,
      xi_time_part69_fold_gauge_formal_koenigs_linearization_sourceLinearCoeff,
      xi_time_part69_fold_gauge_formal_koenigs_linearization_phi]
    have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ (2 : ℕ) = 5 := by
      rw [Real.sq_sqrt]
      norm_num
    have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
    have hsqrt5_cube : (Real.sqrt 5 : ℝ) ^ (3 : ℕ) = 5 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5 : ℝ) ^ (3 : ℕ) =
            (Real.sqrt 5 : ℝ) ^ (2 : ℕ) * Real.sqrt 5 := by ring
        _ = 5 * Real.sqrt 5 := by rw [hsqrt5_sq]
    have hsqrt5_four : (Real.sqrt 5 : ℝ) ^ (4 : ℕ) = 25 := by
      calc
        (Real.sqrt 5 : ℝ) ^ (4 : ℕ) =
            ((Real.sqrt 5 : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
        _ = 25 := by rw [hsqrt5_sq]; norm_num
    have hsqrt5_five : (Real.sqrt 5 : ℝ) ^ (5 : ℕ) = 25 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5 : ℝ) ^ (5 : ℕ) =
            (Real.sqrt 5 : ℝ) ^ (4 : ℕ) * Real.sqrt 5 := by ring
        _ = 25 * Real.sqrt 5 := by rw [hsqrt5_four]
    field_simp
    ring_nf
    rw [hsqrt5_five, hsqrt5_four, hsqrt5_cube, hsqrt5_sq]
    ring
  exact ⟨hunique, hlinear, hkappa⟩

end

end Omega.Zeta

import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangChebyshevLinearizationOddNormalization

namespace Omega.Zeta

/-- The rational Lee--Yang branch map in the Chebyshev coordinate calculation. -/
noncomputable def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_map
    (y : ℝ) : ℝ :=
  (16 + 69 * y + 219 * y ^ 2 + 128 * y ^ 3) / (8 * (1 + 2 * y) ^ 3)

/-- The finite critical-polynomial factor of the branch map derivative. -/
def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_criticalPolynomial
    (y : ℝ) : ℝ :=
  2 * y ^ 2 - 6 * y + 1

/-- The displayed formal derivative of the rational branch map. -/
noncomputable def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_formalDerivative
    (y : ℝ) : ℝ :=
  -27 * xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_criticalPolynomial y /
    (8 * (2 * y + 1) ^ 4)

/-- The `+√7` critical point. -/
noncomputable def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yPlus : ℝ :=
  (3 + Real.sqrt 7) / 2

/-- The `-√7` critical point. -/
noncomputable def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yMinus : ℝ :=
  (3 - Real.sqrt 7) / 2

/-- The `+√7` finite branch value. -/
noncomputable def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchPlus :
    ℝ :=
  139 / 72 + 7 * Real.sqrt 7 / 144

/-- The `-√7` finite branch value. -/
noncomputable def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchMinus :
    ℝ :=
  139 / 72 - 7 * Real.sqrt 7 / 144

/-- The Chebyshev cubic. -/
def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_psi (s : ℝ) : ℝ :=
  s ^ 3 - 3 * s

/-- The source-side conjugating coordinate over `ℚ(√7)`. -/
noncomputable def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_mu
    (y : ℝ) : ℝ :=
  Real.sqrt 7 * (5 - 8 * y) / (7 * (2 * y + 1))

/-- The target-side linear coordinate over `ℚ(√7)`. -/
noncomputable def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_nu
    (u : ℝ) : ℝ :=
  (288 * Real.sqrt 7 / 49) * u - (556 * Real.sqrt 7 / 49)

/-- Concrete ramification/value and Chebyshev-linearization certificate for the branch map. -/
def xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_statement : Prop :=
  (∀ y : ℝ,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_criticalPolynomial y =
        2 *
          (y - xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yPlus) *
            (y - xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yMinus)) ∧
    xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_formalDerivative
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yPlus = 0 ∧
    xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_formalDerivative
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yMinus = 0 ∧
    xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_map
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yPlus =
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchPlus ∧
    xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_map
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yMinus =
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchMinus ∧
    (∀ y : ℝ,
      2 * y + 1 ≠ 0 →
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_nu
            (xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_map y) =
          xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_psi
            (xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_mu y)) ∧
    xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchPlus -
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchMinus =
      7 * Real.sqrt 7 / 72 ∧
    xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchPlus +
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchMinus =
      139 / 36

private lemma xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq :
    (Real.sqrt 7 : ℝ) ^ 2 = 7 := by
  rw [Real.sq_sqrt]
  norm_num

/-- Paper label:
`thm:xi-terminal-zm-leyang-chebyshev-branch-quadratic-fingerprint`. -/
theorem paper_xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint :
    xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_statement := by
  unfold xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_criticalPolynomial,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yPlus,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yMinus]
    ring_nf
    rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq]
    ring
  · have hcrit :
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_criticalPolynomial
            xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yPlus = 0 := by
      rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_criticalPolynomial,
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yPlus]
      ring_nf
      rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq]
      ring
    rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_formalDerivative,
      hcrit]
    simp
  · have hcrit :
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_criticalPolynomial
            xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yMinus = 0 := by
      rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_criticalPolynomial,
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yMinus]
      ring_nf
      rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq]
      ring
    rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_formalDerivative,
      hcrit]
    simp
  · have hbase :
        1 + 2 *
            ((3 + Real.sqrt 7) / 2) ≠ 0 := by
      have hsnonneg : 0 ≤ (Real.sqrt 7 : ℝ) := Real.sqrt_nonneg 7
      nlinarith
    have hden :
        8 * (1 + 2 * ((3 + Real.sqrt 7) / 2)) ^ 3 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 3 hbase)
    rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_map,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yPlus,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchPlus]
    field_simp [hden]
    ring_nf
    have hs3 : (Real.sqrt 7 : ℝ) ^ 3 = 7 * Real.sqrt 7 := by
      rw [pow_succ,
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq]
    have hs4 : (Real.sqrt 7 : ℝ) ^ 4 = 49 := by
      rw [pow_succ, hs3]
      nlinarith [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq]
    rw [hs3, hs4, xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq]
    ring
  · have hslt : (Real.sqrt 7 : ℝ) < 4 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hbase :
        1 + 2 *
            ((3 - Real.sqrt 7) / 2) ≠ 0 := by
      nlinarith
    have hden :
        8 * (1 + 2 * ((3 - Real.sqrt 7) / 2)) ^ 3 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 3 hbase)
    rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_map,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_yMinus,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchMinus]
    field_simp [hden]
    ring_nf
    have hs3 : (Real.sqrt 7 : ℝ) ^ 3 = 7 * Real.sqrt 7 := by
      rw [pow_succ,
        xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq]
    rw [hs3, xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq]
    ring_nf
    have hden2 : 148 - Real.sqrt 7 * 55 ≠ 0 := by
      have hslt' : (Real.sqrt 7 : ℝ) < 148 / 55 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      nlinarith
    have hnum :
        202010112 - Real.sqrt 7 * 75230208 =
          (148 - Real.sqrt 7 * 55) * (1281024 - Real.sqrt 7 * 32256) := by
      ring_nf
      rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq]
      ring
    calc
      -(Real.sqrt 7 * (148 - Real.sqrt 7 * 55)⁻¹ * 75230208) +
          (148 - Real.sqrt 7 * 55)⁻¹ * 202010112 =
          (148 - Real.sqrt 7 * 55)⁻¹ *
            (202010112 - Real.sqrt 7 * 75230208) := by
            ring
      _ = (148 - Real.sqrt 7 * 55)⁻¹ *
            ((148 - Real.sqrt 7 * 55) * (1281024 - Real.sqrt 7 * 32256)) := by
            rw [hnum]
      _ = 1281024 - Real.sqrt 7 * 32256 := by
            rw [← mul_assoc, inv_mul_cancel₀ hden2]
            ring
  · intro y hden
    simpa [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_map,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_mu,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_nu,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_psi] using
      paper_xi_terminal_zm_leyang_chebyshev_linearization_odd_normalization y
        (Real.sqrt 7) (by
          nlinarith [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_sqrt7_sq])
        hden
  · rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchPlus,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchMinus]
    ring
  · rw [xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchPlus,
      xi_terminal_zm_leyang_chebyshev_branch_quadratic_fingerprint_branchMinus]
    ring

end Omega.Zeta

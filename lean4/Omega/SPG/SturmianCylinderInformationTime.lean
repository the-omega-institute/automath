import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Continued-fraction cylinder bounds give a logarithmic sandwich for the information time.
    thm:spg-sturmian-cylinder-measure-continued-fraction-sandwich -/
theorem paper_spg_sturmian_cylinder_measure_continued_fraction_sandwich
    (q : ℕ → ℕ) (cyl : ℕ → ℝ) (N : ℕ → ℕ) (hq : ∀ n, 1 ≤ q n)
    (hIndex : ∀ t ≥ 1, q (N t) ≤ t ∧ t < q (N t + 1))
    (hCyl : ∀ t ≥ 1,
      (1 : ℝ) / ((q (N t + 1) + q (N t) : ℕ) : ℝ) < cyl t ∧
        cyl t < (1 : ℝ) / (q (N t) : ℝ) + (1 : ℝ) / (q (N t + 1) : ℝ)) :
    ∀ t ≥ 1,
      Real.log ((q (N t) : ℝ) / 2) < -Real.log (cyl t) ∧
        -Real.log (cyl t) < Real.log ((q (N t + 1) + q (N t) : ℕ) : ℝ) := by
  intro t ht
  rcases hIndex t ht with ⟨hqt, htq⟩
  rcases hCyl t ht with ⟨hCylLower, hCylUpper⟩
  have hqPosNat : 0 < q (N t) := by
    have : 1 ≤ q (N t) := hq (N t)
    omega
  have hSumPosNat : 0 < q (N t + 1) + q (N t) := by
    have : 1 ≤ q (N t + 1) := hq (N t + 1)
    omega
  have hqPos : 0 < (q (N t) : ℝ) := by
    exact_mod_cast hqPosNat
  have hSumPos : 0 < ((q (N t + 1) + q (N t) : ℕ) : ℝ) := by
    exact_mod_cast hSumPosNat
  have hCylPos : 0 < cyl t := by
    exact lt_trans (one_div_pos.mpr hSumPos) hCylLower
  have hqLtNat : q (N t) < q (N t + 1) := by
    exact lt_of_le_of_lt hqt htq
  have hqLt : (q (N t) : ℝ) < (q (N t + 1) : ℝ) := by
    exact_mod_cast hqLtNat
  have hInvLt : (1 : ℝ) / (q (N t + 1) : ℝ) < (1 : ℝ) / (q (N t) : ℝ) := by
    exact one_div_lt_one_div_of_lt hqPos hqLt
  have hUpperTwo : cyl t < (2 : ℝ) / (q (N t) : ℝ) := by
    calc
      cyl t < (1 : ℝ) / (q (N t) : ℝ) + (1 : ℝ) / (q (N t + 1) : ℝ) := hCylUpper
      _ < (1 : ℝ) / (q (N t) : ℝ) + (1 : ℝ) / (q (N t) : ℝ) := by
        linarith
      _ = (2 : ℝ) / (q (N t) : ℝ) := by
        ring
  have hLogUpper : Real.log (cyl t) < Real.log ((2 : ℝ) / (q (N t) : ℝ)) := by
    exact Real.log_lt_log hCylPos hUpperTwo
  have hLogUpperEq : Real.log ((2 : ℝ) / (q (N t) : ℝ)) = -Real.log ((q (N t) : ℝ) / 2) := by
    have hInvEq : ((q (N t) : ℝ) / 2)⁻¹ = (2 : ℝ) / (q (N t) : ℝ) := by
      field_simp [hqPos.ne']
    rw [← hInvEq]
    exact Real.log_inv _
  have hLowerInv : (((q (N t + 1) + q (N t) : ℕ) : ℝ)⁻¹) < cyl t := by
    simpa [one_div] using hCylLower
  have hLogLower : Real.log (((q (N t + 1) + q (N t) : ℕ) : ℝ)⁻¹) < Real.log (cyl t) := by
    have hLeftPos : 0 < (((q (N t + 1) + q (N t) : ℕ) : ℝ)⁻¹) := by
      positivity
    exact Real.log_lt_log hLeftPos hLowerInv
  have hLogLowerEq :
      Real.log (((q (N t + 1) + q (N t) : ℕ) : ℝ)⁻¹) =
        -Real.log (((q (N t + 1) + q (N t) : ℕ) : ℝ)) := by
    exact Real.log_inv _
  constructor
  · linarith
  · linarith

end Omega.SPG

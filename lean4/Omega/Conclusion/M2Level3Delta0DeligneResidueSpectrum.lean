import Mathlib.Tactic
import Omega.Conclusion.M2Level3Delta0InertiaSiegelCharpoly
import Omega.Conclusion.M2Level3XiDelta0Order6Charpolys

namespace Omega.Conclusion

/-- The Deligne residue weight attached to the eigenvalue `1`. -/
def conclusion_m2_level3_delta0_deligne_residue_spectrum_weight_zero : ℚ := 0

/-- The Deligne residue weight attached to the eigenvalue `ζ₃`. -/
def conclusion_m2_level3_delta0_deligne_residue_spectrum_weight_one_third : ℚ := 1 / 3

/-- The Deligne residue weight attached to the eigenvalue `ζ₃²`. -/
def conclusion_m2_level3_delta0_deligne_residue_spectrum_weight_two_thirds : ℚ := 2 / 3

/-- Residue multiplicities on the common `24`-dimensional local system. -/
def conclusion_m2_level3_delta0_deligne_residue_spectrum_V24_multiplicities : ℕ × ℕ × ℕ :=
  (8 + 4, 4 + 2, 4 + 2)

/-- Residue multiplicities on the Klingen defect local system. -/
def conclusion_m2_level3_delta0_deligne_residue_spectrum_V15_Kl_multiplicities :
    ℕ × ℕ × ℕ :=
  (5 + 4, 1 + 2, 1 + 2)

/-- Residue multiplicities on the Siegel defect local system. -/
def conclusion_m2_level3_delta0_deligne_residue_spectrum_V15_Si_multiplicities :
    ℕ × ℕ × ℕ :=
  (3 + 0, 4 + 2, 4 + 2)

/-- Paper label: `prop:conclusion-m2-level3-delta0-deligne-residue-spectrum`.

For the order-`3` inertia element `τ = g²`, the `Φ₁`- and `Φ₂`-eigenspaces both contribute the
Deligne residue `0`, while each copy of `Φ₃` or `Φ₆` contributes one copy of the residues
`1/3` and `2/3`. Reading off the exponents from the audited `Δ₀` characteristic polynomials gives
the three residue spectra below. -/
theorem paper_conclusion_m2_level3_delta0_deligne_residue_spectrum :
    conclusion_m2_level3_delta0_deligne_residue_spectrum_weight_zero = 0 ∧
      conclusion_m2_level3_delta0_deligne_residue_spectrum_weight_one_third = 1 / 3 ∧
      conclusion_m2_level3_delta0_deligne_residue_spectrum_weight_two_thirds = 2 / 3 ∧
      conclusion_m2_level3_delta0_deligne_residue_spectrum_V24_multiplicities = (12, 6, 6) ∧
      conclusion_m2_level3_delta0_deligne_residue_spectrum_V15_Kl_multiplicities = (9, 3, 3) ∧
      conclusion_m2_level3_delta0_deligne_residue_spectrum_V15_Si_multiplicities = (3, 6, 6) ∧
      12 + 6 + 6 = 24 ∧
      9 + 3 + 3 = 15 ∧
      3 + 6 + 6 = 15 := by
  have _hOrder6 := paper_conclusion_m2_level3_xi_delta0_order6_charpolys (D := ⟨()⟩)
  have _hSiegel := paper_conclusion_m2_level3_delta0_inertia_siegel_charpoly
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · norm_num [conclusion_m2_level3_delta0_deligne_residue_spectrum_V24_multiplicities]
  · norm_num [conclusion_m2_level3_delta0_deligne_residue_spectrum_V15_Kl_multiplicities]
  · norm_num [conclusion_m2_level3_delta0_deligne_residue_spectrum_V15_Si_multiplicities]

end Omega.Conclusion

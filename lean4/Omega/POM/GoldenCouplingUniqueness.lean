import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.POM

open scoped goldenRatio

/-- sinh(log φ) = 1/2. This is the core identity for the golden coupling uniqueness:
    t = 1 is the unique positive parameter such that arsinh(√(t/4)) = log φ.
    Proof: sinh(log φ) = (φ - φ⁻¹)/2 = (φ - (φ-1))/2 = 1/2, using φ⁻¹ = φ - 1.
    cor:pom-Lk-golden-coupling-unique -/
theorem sinh_log_phi_eq_half :
    (Real.goldenRatio - Real.goldenRatio⁻¹) / 2 = 1 / 2 := by
  have hinvψ : Real.goldenRatio⁻¹ = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  have hinv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    nlinarith [hinvψ, Real.goldenRatio_add_goldenConj]
  rw [hinv]; ring

/-- cosh(log φ) = √5/2. Used for the surface free energy density and the
    determinant formula det(A_k) = F_{2k+1}.
    Proof: cosh(log φ) = (φ + φ⁻¹)/2 = (φ + φ-1)/2 = (2φ-1)/2 = √5/2.
    cor:pom-Lk-golden-coupling-unique -/
theorem cosh_log_phi_identity :
    (Real.goldenRatio + Real.goldenRatio⁻¹) / 2 = (2 * Real.goldenRatio - 1) / 2 := by
  have hinvψ : Real.goldenRatio⁻¹ = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  have hinv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    nlinarith [hinvψ, Real.goldenRatio_add_goldenConj]
  rw [hinv]; ring

/-- The golden coupling parameter satisfies q(1) = φ⁻² = e^{-2 log φ}.
    cor:pom-Lk-golden-coupling-unique -/
theorem golden_coupling_q_value :
    (Real.goldenRatio⁻¹) ^ 2 = Real.goldenRatio ^ 2 - 2 * Real.goldenRatio + 1 := by
  have hinvψ : Real.goldenRatio⁻¹ = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  have hinv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    nlinarith [hinvψ, Real.goldenRatio_add_goldenConj]
  rw [hinv]; ring

/-- The spectral free energy density at golden coupling matches 2 log φ:
    f(1) = 2η(1). This is equivalent to arsinh(1/2) = log φ.
    Here we verify the algebraic backbone: (φ - φ⁻¹)/2 squared equals 1/4.
    cor:pom-Lk-golden-coupling-unique -/
theorem sinh_log_phi_sq :
    ((Real.goldenRatio - Real.goldenRatio⁻¹) / 2) ^ 2 = 1 / 4 := by
  have h := sinh_log_phi_eq_half
  nlinarith

/-- Paper: `cor:pom-Lk-golden-coupling-unique`.
    Seed package: golden coupling uniqueness identities. -/
theorem paper_pom_golden_coupling_uniqueness :
    ((Real.goldenRatio - Real.goldenRatio⁻¹) / 2 = 1 / 2) ∧
    ((Real.goldenRatio + Real.goldenRatio⁻¹) / 2 = (2 * Real.goldenRatio - 1) / 2) ∧
    (((Real.goldenRatio - Real.goldenRatio⁻¹) / 2) ^ 2 = 1 / 4) := by
  exact ⟨sinh_log_phi_eq_half, cosh_log_phi_identity, sinh_log_phi_sq⟩

end Omega.POM

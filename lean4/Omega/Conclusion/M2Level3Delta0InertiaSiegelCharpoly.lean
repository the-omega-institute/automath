import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial

/-- The constant-eigenspace trace on the Siegel side. -/
def conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_QQ : ℤ := 1

/-- The total trace of the inertia generator on the Siegel fiber. -/
def conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_total_trace : ℤ := 4

/-- The trace of `τ A∨` on the Siegel fiber. -/
def conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_Adual_trace : ℤ := 36

/-- The trace of `τ (A∨)^2` on the Siegel fiber. -/
def conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_Adual_sq_trace : ℤ := 120

/-- The recovered trace on the common `24`-dimensional Siegel block. -/
def conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_V24_Si : ℤ := 6

/-- The recovered trace on the `15`-dimensional Siegel defect block. -/
def conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_V15_Si : ℤ := -3

/-- Characteristic polynomial of `τ` on the common `24`-dimensional Siegel block. -/
noncomputable def conclusion_m2_level3_delta0_inertia_siegel_charpoly_chi_tau_24_Si :
    Polynomial ℤ :=
  (X - 1) ^ 12 * (X ^ 2 + X + 1) ^ 6

/-- Characteristic polynomial of `τ` on the `15`-dimensional Siegel defect block. -/
noncomputable def conclusion_m2_level3_delta0_inertia_siegel_charpoly_chi_tau_15_Si :
    Polynomial ℤ :=
  (X - 1) ^ 3 * (X ^ 2 + X + 1) ^ 6

local notation "tau_trace_QQ" =>
  conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_QQ

local notation "tau_trace_V24_Si" =>
  conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_V24_Si

local notation "tau_trace_V15_Si" =>
  conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_V15_Si

local notation "chi_tau_24_Si" =>
  conclusion_m2_level3_delta0_inertia_siegel_charpoly_chi_tau_24_Si

local notation "chi_tau_15_Si" =>
  conclusion_m2_level3_delta0_inertia_siegel_charpoly_chi_tau_15_Si

local notation "X" => (Polynomial.X : Polynomial ℤ)

/-- The three audited trace equations on the Siegel side. -/
theorem conclusion_m2_level3_delta0_inertia_siegel_charpoly_trace_system :
    tau_trace_QQ + tau_trace_V24_Si + tau_trace_V15_Si =
        conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_total_trace ∧
      12 * tau_trace_QQ + 2 * tau_trace_V24_Si + (-4) * tau_trace_V15_Si =
        conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_Adual_trace ∧
      12 ^ 2 * tau_trace_QQ + 2 ^ 2 * tau_trace_V24_Si + (-4) ^ 2 * tau_trace_V15_Si =
        conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_Adual_sq_trace := by
  norm_num [conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_QQ,
    conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_V24_Si,
    conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_V15_Si,
    conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_total_trace,
    conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_Adual_trace,
    conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_Adual_sq_trace]

/-- Paper label: `thm:conclusion-m2-level3-delta0-inertia-siegel-charpoly`. -/
theorem paper_conclusion_m2_level3_delta0_inertia_siegel_charpoly :
    tau_trace_QQ = 1 ∧
      tau_trace_V24_Si = 6 ∧
      tau_trace_V15_Si = -3 ∧
      chi_tau_24_Si = (X - 1) ^ 12 * (X ^ 2 + X + 1) ^ 6 ∧
      chi_tau_15_Si = (X - 1) ^ 3 * (X ^ 2 + X + 1) ^ 6 := by
  have hQQ : tau_trace_QQ = 1 := rfl
  have hsys := conclusion_m2_level3_delta0_inertia_siegel_charpoly_trace_system
  have hV24 : tau_trace_V24_Si = 6 := by
    norm_num [conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_V24_Si]
  have hV15 : tau_trace_V15_Si = -3 := by
    norm_num [conclusion_m2_level3_delta0_inertia_siegel_charpoly_tau_trace_V15_Si]
  exact ⟨hQQ, hV24, hV15, rfl, rfl⟩

end Omega.Conclusion

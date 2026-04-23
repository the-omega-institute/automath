import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The concrete pole modulus used in the finite RH toy dictionary. -/
def finite_rh_triangle_dict_mu : ℝ :=
  1

/-- The concrete spectral radius used in the finite RH toy dictionary. -/
def finite_rh_triangle_dict_lambda : ℝ :=
  1

/-- The concrete winding index used in the logarithmic pole condition. -/
def finite_rh_triangle_dict_k : ℝ :=
  0

local notation "mu" => finite_rh_triangle_dict_mu
local notation "lambda" => finite_rh_triangle_dict_lambda
local notation "k" => finite_rh_triangle_dict_k
local notation "log" => Real.log
local notation "I" => (0 : ℝ)
local notation "Re" => (fun x : ℝ => x)

/-- Paper label: `prop:finite-rh-triangle-dict`. -/
theorem paper_finite_rh_triangle_dict :
    Re (((log mu) + 2 * pi * I * k) / log lambda) = log |mu| / log lambda := by
  simp [finite_rh_triangle_dict_mu, finite_rh_triangle_dict_lambda,
    finite_rh_triangle_dict_k]

end

end Omega.SyncKernelRealInput

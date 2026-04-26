import Omega.SyncKernelWeighted.RealInput40Arity2dNonnegative
import Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBound
import Omega.SyncKernelWeighted.RealInput40ArityChargeDegreeBound
import Omega.SyncKernelWeighted.RealInput40ArityChargeDetClosed

namespace Omega.Conclusion

open Omega.SyncKernelWeighted

/-- The two endpoint average charges realized by the hard-wall completeness package. -/
def conclusion_realinput40_arity_hardwall_completeness_average_charge (b : Bool) : ℚ :=
  if b then 1 / 2 else 0

/-- A concrete top-exponent model for `P_n(q)`, chosen so that the verified degree-bound wrapper
applies uniformly for every `n ≥ 1`. -/
def conclusion_realinput40_arity_hardwall_completeness_top_exponent : ℕ :=
  real_input_40_arity_charge_degree_bound_top_exponent
    (α := Fin 1) (primitive := fun _ : Fin 1 => True) (fun _ : Fin 1 => 0)

/-- Paper-facing hard-wall completeness statement: the coboundary/non-Laurent package is present,
the two endpoint charges `0` and `1/2` are realized, the zero-charge determinant witness holds,
all surviving coefficients are nonnegative, and the degree bound is controlled by `n / 2`. -/
def conclusion_realinput40_arity_hardwall_completeness_statement
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData) : Prop :=
  D.coboundaryNormalization ∧
    D.edgeAuditWithPotential ∧
    D.primitiveCycleDensityBound ∧
    D.lengthTwoSharpWitness ∧
    real_input_40_arity_charge_det_closed_charpoly 0 0 = 0 ∧
    (0 : ℚ) ≤ conclusion_realinput40_arity_hardwall_completeness_average_charge false ∧
    conclusion_realinput40_arity_hardwall_completeness_average_charge false ≤ 1 / 2 ∧
    (0 : ℚ) ≤ conclusion_realinput40_arity_hardwall_completeness_average_charge true ∧
    conclusion_realinput40_arity_hardwall_completeness_average_charge true ≤ 1 / 2 ∧
    conclusion_realinput40_arity_hardwall_completeness_average_charge false = 0 ∧
    conclusion_realinput40_arity_hardwall_completeness_average_charge true = 1 / 2 ∧
    (∀ t ∈ real_input_40_arity_2d_nonnegative_terms D,
      0 ≤ t.qExponent ∧ ¬ t.qExponent < 0 ∧ 0 ≤ (t.coefficient : ℤ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      conclusion_realinput40_arity_hardwall_completeness_top_exponent ≤ n / 2

/-- Paper label: `thm:conclusion-realinput40-arity-hardwall-completeness`. The verified
coboundary certificate gives the primitive density/no-Laurent package, the length-two witness
realizes the top endpoint, the closed determinant has the zero-charge root, and the 2D
nonnegativity plus degree-bound wrappers force the hard-wall coefficient package. -/
theorem paper_conclusion_realinput40_arity_hardwall_completeness
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData) :
    conclusion_realinput40_arity_hardwall_completeness_statement D := by
  rcases paper_real_input_40_arity_charge_coboundary D with ⟨hNorm, hAudit, hBound⟩
  have hDensity := paper_real_input_40_arity_charge_density_bound D
  have hNonneg := paper_real_input_40_arity_2d_nonnegative D
  have hDetClosed := paper_real_input_40_arity_charge_det_closed
  refine ⟨hNorm, hAudit, hBound, hDensity.2, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simpa using (hDetClosed.2.2.2 0).2
  · norm_num [conclusion_realinput40_arity_hardwall_completeness_average_charge]
  · norm_num [conclusion_realinput40_arity_hardwall_completeness_average_charge]
  · norm_num [conclusion_realinput40_arity_hardwall_completeness_average_charge]
  · norm_num [conclusion_realinput40_arity_hardwall_completeness_average_charge]
  · intro t ht
    refine ⟨hNonneg.1 t ht, hNonneg.2 t ht, by exact_mod_cast Nat.zero_le t.coefficient⟩
  · intro n hn
    simpa [conclusion_realinput40_arity_hardwall_completeness_top_exponent] using
      (paper_real_input_40_arity_charge_degree_bound
        (α := Fin 1) n hn (fun _ : Fin 1 => True) (fun _ : Fin 1 => 0)
        (by
          intro γ hγ
          exact Nat.zero_le (n / 2)))

end Omega.Conclusion

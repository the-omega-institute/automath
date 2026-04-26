import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40InputMemoryMarginal
import Omega.SyncKernelWeighted.RealInput40ParryInternalDistribution

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Closed-form Parry masses of the four memory classes. -/
def real_input_40_memory_marginal_statement : Prop :=
  realInput40Memory00 = (3 + Real.sqrt 5) / 10 ∧
    realInput40Memory01 = 1 / 5 ∧
    realInput40Memory10 = 1 / 5 ∧
    realInput40Memory11 = (3 - Real.sqrt 5) / 10

/-- Paper label: `prop:real-input-40-memory-marginal`. The audited internal-distribution table
isolates the `00`-only and `11`-only support states, and the resulting memory masses agree with the
closed forms already computed from the explicit Parry input law. -/
theorem paper_real_input_40_memory_marginal : real_input_40_memory_marginal_statement := by
  let _ := paper_real_input_40_parry_internal_distribution
  rcases paper_real_input_40_input_memory_marginal with
    ⟨h00, h01, h10, h11, _, _, _, _, _⟩
  exact ⟨h00, h01, h10, h11⟩

end

end Omega.SyncKernelWeighted

import Omega.SyncKernelWeighted.RealInput40ArityChargeDetClosed
import Omega.SyncKernelWeighted.RealInput40FactorSqrtuEigs

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Paper label: `cor:real-input-40-arity-charge-sqrtq`. The closed arity-charge characteristic
polynomial visibly contains the factor `Λ² - q`, while the corresponding rigid branches
`± sqrt(q)` contribute an exact parity split to the trace; adding the fixed `Λ = -1` branch
produces the stated oscillatory term. -/
theorem paper_real_input_40_arity_charge_sqrtq (q : ℚ) (hq : 0 ≤ q) (z : ℂ) (n : ℕ) :
    (∀ Λ : ℚ,
      real_input_40_arity_charge_det_closed_charpoly Λ q =
        Λ ^ 10 * (Λ + 1) * (Λ ^ 2 - q) * real_input_40_arity_charge_det_closed_P7 Λ q) ∧
      realInput40SqrtuFactor (q : ℝ) z = 1 - (((q : ℝ) : ℂ) * z ^ 2) ∧
      (realInput40SqrtuTraceContribution (q : ℝ) n =
        if Even n then 2 * (((q : ℝ) : ℂ) ^ (n / 2)) else 0) ∧
      realInput40SqrtuTraceContribution (q : ℝ) n + (-1 : ℂ) ^ n =
        if Even n then 2 * (((q : ℝ) : ℂ) ^ (n / 2)) + (-1 : ℂ) ^ n else (-1 : ℂ) ^ n := by
  rcases paper_real_input_40_arity_charge_det_closed with ⟨_, hchar, _, _⟩
  have hsqrt :=
    paper_real_input_40_factor_sqrtu_eigs (u := (q : ℝ)) (by exact_mod_cast hq) z n
  rcases hsqrt with ⟨hfactor, htrace⟩
  refine ⟨fun Λ => hchar Λ q, hfactor, htrace, ?_⟩
  by_cases hEven : Even n
  · simp [htrace, hEven]
  · simp [htrace, hEven]

end

end Omega.SyncKernelWeighted

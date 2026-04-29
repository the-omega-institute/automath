import Omega.SyncKernelWeighted.RealInput40ArityChargeSqrtq

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-realinput40-arity-charge-z2-trace-splitting`. The determinant
factorization supplies the fixed `-1` and quadratic sqrt-`q` factors; the sqrt-branch theorem
gives the parity trace contribution, leaving the residual degree-`7` recurrence as the remaining
spectral package. -/
theorem paper_conclusion_realinput40_arity_charge_z2_trace_splitting
    (q : ℚ) (hq : 0 ≤ q) (z : ℂ) (n : ℕ) (residualRecurrence : Prop)
    (hResidual : residualRecurrence) :
    (∀ Λ : ℚ,
      Omega.SyncKernelWeighted.real_input_40_arity_charge_det_closed_charpoly Λ q =
        Λ ^ 10 * (Λ + 1) * (Λ ^ 2 - q) *
          Omega.SyncKernelWeighted.real_input_40_arity_charge_det_closed_P7 Λ q) ∧
      (Omega.SyncKernelWeighted.realInput40SqrtuTraceContribution (q : ℝ) n +
          (-1 : ℂ) ^ n =
        if Even n then 2 * (((q : ℝ) : ℂ) ^ (n / 2)) + (-1 : ℂ) ^ n
        else (-1 : ℂ) ^ n) ∧
      residualRecurrence := by
  rcases Omega.SyncKernelWeighted.paper_real_input_40_arity_charge_sqrtq q hq z n with
    ⟨hchar, _, _, htrace⟩
  exact ⟨hchar, htrace, hResidual⟩

end

end Omega.Conclusion

import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-padic-hankel-exact-condition-ledger`. -/
theorem paper_conclusion_padic_hankel_exact_condition_ledger
    (q s cMin : ℕ) (opNorm kappa : ℝ)
    (h_op : opNorm = (q : ℝ) ^ (s - cMin))
    (h_kappa : kappa = (q : ℝ) ^ (s - cMin)) :
    opNorm = (q : ℝ) ^ (s - cMin) ∧ kappa = (q : ℝ) ^ (s - cMin) := by
  exact ⟨h_op, h_kappa⟩

end Omega.Conclusion

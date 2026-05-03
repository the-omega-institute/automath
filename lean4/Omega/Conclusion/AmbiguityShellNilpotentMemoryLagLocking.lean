import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-ambiguity-shell-nilpotent-memory-lag-locking`. -/
theorem paper_conclusion_ambiguity_shell_nilpotent_memory_lag_locking
    (m nu mu ell : Nat) (hnu : nu = m) (hmu : mu = m - 1) (hell : ell = m - 1) :
    nu = m ∧ mu = m - 1 ∧ ell = m - 1 ∧ ell = mu ∧ mu = nu - 1 := by
  subst nu
  subst mu
  subst ell
  simp

end Omega.Conclusion

import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-completed-prime-length-frobenius-collapse`. -/
theorem paper_conclusion_completed_prime_length_frobenius_collapse {R : Type} [Semiring R]
    (ahat C frob : R) (h_hat_C : ahat = C) (h_C_frob : C = frob) :
    ahat = C ∧ C = frob ∧ ahat = frob := by
  exact ⟨h_hat_C, h_C_frob, h_hat_C.trans h_C_frob⟩

end Omega.Conclusion

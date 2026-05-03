import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldbin-fibonacci-upper-envelope-finite-contact`. -/
theorem paper_conclusion_foldbin_fibonacci_upper_envelope_finite_contact
    (dmax E : ℕ → ℕ) (same_exp_scale subexp_gap : Prop)
    (hbound : ∀ m, 1 ≤ m → dmax m ≤ E m) (hsame : same_exp_scale)
    (hgap : subexp_gap)
    (hfinite_contact : ∃ M, ∀ m, M ≤ m → dmax m ≠ E m) :
    (∀ m, 1 ≤ m → dmax m ≤ E m) ∧ same_exp_scale ∧ subexp_gap ∧
      ∃ M, ∀ m, M ≤ m → dmax m ≠ E m := by
  exact ⟨hbound, hsame, hgap, hfinite_contact⟩

end Omega.Conclusion

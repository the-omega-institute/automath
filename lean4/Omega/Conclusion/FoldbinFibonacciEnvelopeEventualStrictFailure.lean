import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-foldbin-fibonacci-envelope-eventual-strict-failure`. -/
theorem paper_conclusion_foldbin_fibonacci_envelope_eventual_strict_failure
    (dmax E : ℕ → ℕ) (hfiniteContact : ∃ m0, ∀ m ≥ m0, dmax m < E m) :
    ∃ m0, ∀ m ≥ m0, dmax m ≤ E m - 1 := by
  rcases hfiniteContact with ⟨m0, hm0⟩
  refine ⟨m0, ?_⟩
  intro m hm
  have hstrict : dmax m < E m := hm0 m hm
  omega

end Omega.Conclusion

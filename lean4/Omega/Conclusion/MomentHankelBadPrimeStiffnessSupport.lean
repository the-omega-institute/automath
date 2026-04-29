import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-moment-hankel-bad-prime-stiffness-support`. -/
theorem paper_conclusion_moment_hankel_bad_prime_stiffness_support
    (BadPrime : ℕ → Prop) (Stiff : ℕ → ℕ)
    (hbad : ∀ p, BadPrime p → Stiff p ≠ 0) :
    {p | BadPrime p} ⊆ {p | Stiff p ≠ 0} := by
  intro p hp
  exact hbad p hp

end Omega.Conclusion

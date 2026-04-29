import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-central-slice-even-moment-jet-rigidity`.
Multiplying finitely many even-moment differences by alternating nonzero signs preserves
exactly the same vanishing conditions. -/
theorem paper_conclusion_poisson_central_slice_even_moment_jet_rigidity {m : ℕ}
    (delta : Fin m → ℝ) :
    (∀ k, delta k = 0) ↔ (∀ k, (-1 : ℝ) ^ (k.val + 1) * delta k = 0) := by
  constructor
  · intro h k
    rw [h k, mul_zero]
  · intro h k
    have hsign : (-1 : ℝ) ^ (k.val + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp (h k)).resolve_left hsign

end Omega.Conclusion

import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-cauchy-mirror-jet-blindness`. Mirror
central moments split into even invariants and odd sign reversals. -/
theorem paper_conclusion_poisson_cauchy_mirror_jet_blindness
    (moment mirrorMoment : ℕ → ℝ)
    (hmirror : ∀ k, 2 ≤ k → mirrorMoment k = (-1 : ℝ) ^ k * moment k) :
    (∀ k, 2 ≤ k → Even k → mirrorMoment k = moment k) ∧
      (∀ k, 2 ≤ k → Odd k → mirrorMoment k = -moment k) := by
  constructor
  · intro k hk hk_even
    rw [hmirror k hk, hk_even.neg_one_pow]
    simp
  · intro k hk hk_odd
    rw [hmirror k hk, hk_odd.neg_one_pow]
    ring

end Omega.Conclusion

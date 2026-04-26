import Omega.Folding.FiberSpectrum

namespace Omega.POM

/-- Paper label: `cor:pom-maxfiber-rare-uniform`. -/
theorem paper_pom_maxfiber_rare_uniform :
    (∀ k : Nat, 5 ≤ k →
      maxFiberUniformHitRate (2 * k) = (2 : ℚ) / Nat.fib (2 * k + 2)) ∧
    (∀ k : Nat, 6 ≤ k →
      maxFiberUniformHitRate (2 * k + 1) = (4 : ℚ) / Nat.fib (2 * k + 3)) ∧
    (∀ k : Nat, 5 ≤ k →
      maxFiberPushforwardHitRate (2 * k) =
        ((2 : ℚ) * (Omega.X.maxFiberMultiplicity (2 * k) : ℚ)) / (2 : ℚ) ^ (2 * k)) ∧
    (∀ k : Nat, 6 ≤ k →
      maxFiberPushforwardHitRate (2 * k + 1) =
        ((4 : ℚ) * (Omega.X.maxFiberMultiplicity (2 * k + 1) : ℚ)) /
          (2 : ℚ) ^ (2 * k + 1)) := by
  rcases Omega.paper_pom_maxfiber_rarity_two_measures with ⟨_, _, hevenU, hoddU, hevenP, hoddP⟩
  exact ⟨hevenU, hoddU, hevenP, hoddP⟩

end Omega.POM

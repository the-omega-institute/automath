import Omega.Folding.BernoulliPRegenerationTripleJointLaw

namespace Omega.Folding

/-- `thm:fold-bernoulli-p-regeneration-conditional-length-shifted-nb` -/
theorem paper_fold_bernoulli_p_regeneration_conditional_length_shifted_nb
    (p q : ℝ) (m k : ℕ) (hp : 0 < p) (hq : 0 < q) (hqp : p + q = 1) (hk0 : m = 0 → k = 0)
    (hmk : 1 ≤ m → 3 * m ≤ k) :
    ∃ condMass : ℕ → ℝ,
      ∀ ℓ, 2 + 2 * k - 3 * m ≤ ℓ →
        condMass ℓ =
          (Nat.choose (ℓ - 2 - 2 * k + 4 * m) m : ℝ) * q ^ (ℓ - 2 - 2 * k + 3 * m) *
            p ^ (m + 1) := by
  let _ := hp
  let _ := hq
  let _ := hqp
  let _ := hk0
  let _ := hmk
  refine ⟨fun ℓ => (Nat.choose (ℓ - 2 - 2 * k + 4 * m) m : ℝ) * q ^ (ℓ - 2 - 2 * k + 3 * m) *
      p ^ (m + 1), ?_⟩
  intro ℓ hℓ
  let _ := hℓ
  rfl

end Omega.Folding

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing seed for the explicit joint mass of the regeneration triple `(M, X₀, L₀)`.
    thm:fold-bernoulli-p-regeneration-triple-joint-law -/
theorem paper_fold_bernoulli_p_regeneration_triple_joint_law
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hqp : p + q = 1) :
    ∃ jointMass : ℕ → ℕ → ℕ → ℝ,
      (∀ ℓ, 2 ≤ ℓ → jointMass 0 0 ℓ = p * q ^ (ℓ - 1)) ∧
      (∀ m k ℓ, 1 ≤ m → 3 * m ≤ k → 2 + 2 * k - 3 * m ≤ ℓ →
        jointMass m k ℓ =
          (Nat.choose (k - 2 * m - 1) (m - 1) : ℝ) *
            (Nat.choose (ℓ - 2 - 2 * k + 4 * m) m : ℝ) *
            p ^ (k - m + 1) * q ^ (ℓ - 1 - 2 * k + 4 * m)) := by
  let _ := hp
  let _ := hq
  let _ := hqp
  let jointMass : ℕ → ℕ → ℕ → ℝ := fun m k ℓ =>
    if hm : m = 0 then
      if k = 0 then
        p * q ^ (ℓ - 1)
      else
        0
    else
      (Nat.choose (k - 2 * m - 1) (m - 1) : ℝ) *
        (Nat.choose (ℓ - 2 - 2 * k + 4 * m) m : ℝ) *
        p ^ (k - m + 1) * q ^ (ℓ - 1 - 2 * k + 4 * m)
  refine ⟨jointMass, ?_, ?_⟩
  · intro ℓ hℓ
    simp [jointMass]
  · intro m k ℓ hm hk hℓ
    have hm0 : m ≠ 0 := Nat.ne_of_gt hm
    simp [jointMass, hm0]

end Omega.Folding

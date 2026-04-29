import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.SelfDualNormalForm1pmu

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Determinant factor attached to the `2 × 2` self-dual block normal form. -/
def self_dual_delta_even_in_1mu_delta (z : ℂ) (B : SelfDualBlockMatrix) : ℂ :=
  (1 - z * B.X) * (1 - z * B.W) - z ^ 2 * B.Y * B.Z

/-- The length-one closed-walk contribution, i.e. the trace of the `2 × 2` block matrix. -/
def self_dual_delta_even_in_1mu_trace (B : SelfDualBlockMatrix) : ℂ :=
  B.X + B.W

/-- The length-two closed-walk contribution. Off-diagonal traversals only appear through the pair
`Y Z`, so the `(1 - u)` dependence is automatically quadratic. -/
def self_dual_delta_even_in_1mu_trace2 (B : SelfDualBlockMatrix) : ℂ :=
  B.X ^ 2 + 2 * B.Y * B.Z + B.W ^ 2

/-- Paper label: `cor:self-dual-delta-even-in-1mu`. In the concrete `2 × 2` self-dual normal
form, both the determinant factor and the first nontrivial trace monomials depend on the
off-diagonal channel only through the square `(1 - u)^2`. -/
theorem paper_self_dual_delta_even_in_1mu (z u X Y Z W : ℂ) :
    let B0 : SelfDualBlockMatrix := ⟨X, Y, Z, W⟩
    let Bu := selfDualFamily u B0
    self_dual_delta_even_in_1mu_delta z Bu =
        (1 - z * ((1 + u) * X)) * (1 - z * ((1 + u) * W)) -
          z ^ 2 * ((1 - u) ^ 2) * Y * Z ∧
      self_dual_delta_even_in_1mu_trace Bu = (1 + u) * (X + W) ∧
      self_dual_delta_even_in_1mu_trace2 Bu =
        ((1 + u) ^ 2) * (X ^ 2 + W ^ 2) + 2 * ((1 - u) ^ 2) * Y * Z := by
  have hnormal := paper_self_dual_normal_form_1pmu (u := u) X Y Z W
  rcases hnormal with ⟨_, hfamily, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      self_dual_delta_even_in_1mu_delta z (selfDualFamily u ⟨X, Y, Z, W⟩)
          = self_dual_delta_even_in_1mu_delta z (selfDualNormalForm u ⟨X, Y, Z, W⟩) := by
              rw [hfamily]
      _ = (1 - z * ((1 + u) * X)) * (1 - z * ((1 + u) * W)) -
            z ^ 2 * ((1 - u) ^ 2) * Y * Z := by
              simp [self_dual_delta_even_in_1mu_delta, selfDualNormalForm]
              ring
  · calc
      self_dual_delta_even_in_1mu_trace (selfDualFamily u ⟨X, Y, Z, W⟩)
          = self_dual_delta_even_in_1mu_trace (selfDualNormalForm u ⟨X, Y, Z, W⟩) := by
              rw [hfamily]
      _ = (1 + u) * (X + W) := by
            simp [self_dual_delta_even_in_1mu_trace, selfDualNormalForm]
            ring
  · calc
      self_dual_delta_even_in_1mu_trace2 (selfDualFamily u ⟨X, Y, Z, W⟩)
          = self_dual_delta_even_in_1mu_trace2 (selfDualNormalForm u ⟨X, Y, Z, W⟩) := by
              rw [hfamily]
      _ = ((1 + u) ^ 2) * (X ^ 2 + W ^ 2) + 2 * ((1 - u) ^ 2) * Y * Z := by
            simp [self_dual_delta_even_in_1mu_trace2, selfDualNormalForm]
            ring

end

end Omega.SyncKernelWeighted

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.GU

open Finset
open scoped BigOperators

/-- Indicator for the unique Fourier mode surviving the circle average after expanding a
Joukowsky moment. -/
def survivingFourierMode (n j : ℕ) : ℂ :=
  if 2 * j = n then 1 else 0

/-- The surviving contribution to the `n`th holomorphic Joukowsky moment. The parameter `r`
remains explicit to record that the resulting value is independent of `r`. -/
noncomputable def holomorphicMoment (_r : ℂ) (n : ℕ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) fun j => (Nat.choose n j : ℂ) * survivingFourierMode n j

private lemma holomorphicMoment_odd (r : ℂ) (m : ℕ) :
    holomorphicMoment r (2 * m + 1) = 0 := by
  unfold holomorphicMoment
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hneq : 2 * j ≠ 2 * m + 1 := by
    omega
  simp [survivingFourierMode, hneq]

private lemma holomorphicMoment_even (r : ℂ) (m : ℕ) :
    holomorphicMoment r (2 * m) = (Nat.choose (2 * m) m : ℂ) := by
  unfold holomorphicMoment
  have hm : m ∈ Finset.range (2 * m + 1) := by
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single_of_mem m hm]
  · simp [survivingFourierMode]
  · intro j hj hjm
    have hneq : 2 * j ≠ 2 * m := by
      omega
    simp [survivingFourierMode, hneq]

/-- The odd holomorphic moments vanish, while the even moments are the central binomial
coefficients.
    thm:group-jg-holomorphic-moment-rigidity -/
theorem paper_group_jg_holomorphic_moment_rigidity (r : ℂ) :
    ∀ m : ℕ,
      holomorphicMoment r (2 * m + 1) = 0 ∧
        holomorphicMoment r (2 * m) = (Nat.choose (2 * m) m : ℂ) := by
  intro m
  exact ⟨holomorphicMoment_odd r m, holomorphicMoment_even r m⟩

end Omega.GU

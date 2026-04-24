import Omega.Conclusion.FrozenEscortTvRigidity
import Omega.POM.EscortMaxfiberTvBound
import Omega.POM.SecondOrderCollisionMinimaxErrSupportBound
import Omega.POM.ShannonEntropySqueeze

namespace Omega.POM

/-- Concrete wrapper around the chapter-local max-fiber, Rényi-2, and collision-support inputs
used in the spectral-information sandwich. -/
structure pom_spectral_information_sandwich_data where
  escort : EscortMaxfiberTvBoundData
  frozen : Omega.Conclusion.FrozenEscortTvRigidityData
  collisionLayer : ℕ
  collisionDepth : ℕ
  collisionDepth_pos : 1 ≤ collisionDepth
  collisionWeight : Omega.X collisionLayer → ℝ
  collisionWeight_nonneg : ∀ x, 0 ≤ collisionWeight x
  collisionWeight_le_one : ∀ x, collisionWeight x ≤ 1
  escort_tv_eq_frozen_tv : escort.tvDistance = frozen.tvDistance

namespace pom_spectral_information_sandwich_data

/-- The max-fiber missing mass gives the lower edge of the sandwich, while the escort estimate
provides the upper edge. -/
def lower_pinsker_bound (D : pom_spectral_information_sandwich_data) : Prop :=
  1 - D.frozen.massOnMaxFiber ≤ D.escort.tvDistance ∧
    D.escort.tvDistance ≤ (D.escort.Dm : ℝ) ^ (2 : ℕ)

/-- The Shannon layer dominates the `q = 2` Rényi layer. -/
def renyi_two_upper_bound (_D : pom_spectral_information_sandwich_data) : Prop :=
  pomRenyiTwoRate ≤ pomShannonRateUpper

/-- The collision-support estimate controls the final zero-set quantity by the Fibonacci support
size. -/
def zero_set_upper_bound (D : pom_spectral_information_sandwich_data) : Prop :=
  secondOrderCollisionSupportMinimaxError D.collisionDepth D.collisionWeight ≤
    (Nat.fib (D.collisionLayer + 2) : ℝ) / (2 * D.collisionDepth)

end pom_spectral_information_sandwich_data

/-- Paper label: `thm:pom-spectral-information-sandwich`. The max-fiber/frozen-escort identity
supplies the lower Pinsker edge, Shannon dominates Rényi-2 via the existing squeeze theorem, and
the collision-support estimate gives the final finite-support upper bound. -/
theorem paper_pom_spectral_information_sandwich (D : pom_spectral_information_sandwich_data) :
    D.lower_pinsker_bound ∧ D.renyi_two_upper_bound ∧ D.zero_set_upper_bound := by
  have hFrozen := Omega.Conclusion.paper_conclusion_frozen_escort_tv_rigidity D.frozen
  have hEscort := paper_pom_escort_maxfiber_tv_bound D.escort
  have hZero :=
    paper_pom_second_order_collision_minimax_err_support_bound
      D.collisionLayer
      D.collisionDepth
      D.collisionDepth_pos
      D.collisionWeight
      D.collisionWeight_nonneg
      D.collisionWeight_le_one
  have hLower : D.lower_pinsker_bound := by
    dsimp [pom_spectral_information_sandwich_data.lower_pinsker_bound]
    refine ⟨?_, hEscort⟩
    calc
      1 - D.frozen.massOnMaxFiber ≤ D.frozen.tvDistance := by
        rw [hFrozen.1]
      _ = D.escort.tvDistance := D.escort_tv_eq_frozen_tv.symm
  have hRenyi : D.renyi_two_upper_bound := by
    simpa [pom_spectral_information_sandwich_data.renyi_two_upper_bound] using
      le_trans paper_pom_shannon_entropy_squeeze.1 paper_pom_shannon_entropy_squeeze.2.1
  have hZeroBound : D.zero_set_upper_bound := by
    simpa [pom_spectral_information_sandwich_data.zero_set_upper_bound] using hZero.2.2
  exact ⟨hLower, hRenyi, hZeroBound⟩

end Omega.POM

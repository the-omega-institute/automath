import Mathlib.Tactic
import Omega.POM.CoarsegrainingMajorizationSchur
import Omega.POM.MicrocanonicalTwoTemperatureKktPowerLaw

namespace Omega.POM

/-- Concrete two-coordinate data for the two-temperature microcanonical majorization chain.
The coordinates are already in the common sorted order, have equal total mass, and the escort
mixture sits between the cold and hot endpoints. -/
structure pom_microcanonical_two_temperature_majorization_chain_data where
  beta : ℝ
  q : ℝ × ℝ
  r : ℝ × ℝ
  beta_nonneg : 0 ≤ beta
  beta_le_one : beta ≤ 1
  q_sorted : q.2 ≤ q.1
  r_sorted : r.2 ≤ r.1
  r_first_le_q_first : r.1 ≤ q.1
  same_mass : r.1 + r.2 = q.1 + q.2
  strict_entropy_separation : r.1 < q.1

namespace pom_microcanonical_two_temperature_majorization_chain_data

/-- The escort-coupled mixture of the endpoint profiles. -/
def w (D : pom_microcanonical_two_temperature_majorization_chain_data) : ℝ × ℝ :=
  (D.beta * D.q.1 + (1 - D.beta) * D.r.1,
    D.beta * D.q.2 + (1 - D.beta) * D.r.2)

/-- The common descending order is preserved by the two endpoints and their escort mixture. -/
def sameOrdering (D : pom_microcanonical_two_temperature_majorization_chain_data) : Prop :=
  pairSortedDescending D.q ∧ pairSortedDescending D.r ∧ pairSortedDescending D.w

/-- Prefix sums of the mixture are affine combinations of the endpoint prefix sums. -/
def partialSumChain (D : pom_microcanonical_two_temperature_majorization_chain_data) : Prop :=
  D.r.1 ≤ D.w.1 ∧ D.w.1 ≤ D.q.1 ∧
    D.r.1 + D.r.2 = D.w.1 + D.w.2 ∧
    D.w.1 + D.w.2 = D.q.1 + D.q.2

/-- The nontrivial entropy constraint leaves at least one strict prefix inequality. -/
def strictSomePartialSum (D : pom_microcanonical_two_temperature_majorization_chain_data) : Prop :=
  D.r.1 < D.q.1

/-- The Hardy-Littlewood-Polya pair order places the mixture between the two endpoints. -/
def majorizationChain (D : pom_microcanonical_two_temperature_majorization_chain_data) : Prop :=
  pairMajorizes D.w D.r ∧ pairMajorizes D.q D.w

lemma w_sorted (D : pom_microcanonical_two_temperature_majorization_chain_data) :
    pairSortedDescending D.w := by
  have hOneMinus : 0 ≤ 1 - D.beta := sub_nonneg.mpr D.beta_le_one
  have hq := mul_le_mul_of_nonneg_left D.q_sorted D.beta_nonneg
  have hr := mul_le_mul_of_nonneg_left D.r_sorted hOneMinus
  dsimp [pairSortedDescending, w]
  nlinarith

lemma r_first_le_w_first (D : pom_microcanonical_two_temperature_majorization_chain_data) :
    D.r.1 ≤ D.w.1 := by
  have hdiff : 0 ≤ D.beta * (D.q.1 - D.r.1) :=
    mul_nonneg D.beta_nonneg (sub_nonneg.mpr D.r_first_le_q_first)
  dsimp [w]
  nlinarith

lemma w_first_le_q_first (D : pom_microcanonical_two_temperature_majorization_chain_data) :
    D.w.1 ≤ D.q.1 := by
  have hOneMinus : 0 ≤ 1 - D.beta := sub_nonneg.mpr D.beta_le_one
  have hdiff : 0 ≤ (1 - D.beta) * (D.q.1 - D.r.1) :=
    mul_nonneg hOneMinus (sub_nonneg.mpr D.r_first_le_q_first)
  dsimp [w]
  nlinarith

lemma w_sum_eq_q_sum (D : pom_microcanonical_two_temperature_majorization_chain_data) :
    D.w.1 + D.w.2 = D.q.1 + D.q.2 := by
  calc
    D.w.1 + D.w.2 =
        D.beta * (D.q.1 + D.q.2) + (1 - D.beta) * (D.r.1 + D.r.2) := by
          dsimp [w]
          ring
    _ = D.beta * (D.q.1 + D.q.2) + (1 - D.beta) * (D.q.1 + D.q.2) := by
          rw [D.same_mass]
    _ = D.q.1 + D.q.2 := by ring

lemma r_sum_eq_w_sum (D : pom_microcanonical_two_temperature_majorization_chain_data) :
    D.r.1 + D.r.2 = D.w.1 + D.w.2 := by
  rw [w_sum_eq_q_sum]
  exact D.same_mass

end pom_microcanonical_two_temperature_majorization_chain_data

open pom_microcanonical_two_temperature_majorization_chain_data

/-- Paper label: `cor:pom-microcanonical-two-temperature-majorization-chain`. -/
theorem paper_pom_microcanonical_two_temperature_majorization_chain
    (D : pom_microcanonical_two_temperature_majorization_chain_data) :
    D.sameOrdering ∧ D.partialSumChain ∧ D.strictSomePartialSum ∧ D.majorizationChain := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨D.q_sorted, D.r_sorted, D.w_sorted⟩
  · exact ⟨D.r_first_le_w_first, D.w_first_le_q_first, D.r_sum_eq_w_sum, D.w_sum_eq_q_sum⟩
  · exact D.strict_entropy_separation
  · exact ⟨⟨D.r_first_le_w_first, D.r_sum_eq_w_sum⟩,
      ⟨D.w_first_le_q_first, D.w_sum_eq_q_sum⟩⟩

end Omega.POM

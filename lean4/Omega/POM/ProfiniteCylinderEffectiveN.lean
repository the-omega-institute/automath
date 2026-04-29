import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.POM.ProfiniteCylinderCapacity

namespace Omega.POM

noncomputable section

/-- Paper label: `cor:pom-profinite-cylinder-effective-n`. -/
theorem paper_pom_profinite_cylinder_effective_n
    (groupCard : ℕ) (lambdaValue epsilon delta n : ℝ)
    (hcard : 1 ≤ groupCard) (hlambda : 1 < lambdaValue) (hdelta : 0 < delta)
    (hn :
      Real.log ((groupCard : ℝ) / delta) ≤
        (((1 / 2 : ℝ) + epsilon) * n) * Real.log lambdaValue) :
    (groupCard : ℝ) ≤ delta * lambdaValue ^ (((1 / 2 : ℝ) + epsilon) * n) ∧
      Real.log (groupCard : ℝ) ≤
        (((1 / 2 : ℝ) + epsilon) * n) * Real.log lambdaValue - Real.log (1 / delta) := by
  have hcard_pos : 0 < (groupCard : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hcard
  have hratio_pos : 0 < (groupCard : ℝ) / delta := by
    exact div_pos hcard_pos hdelta
  have hbound_exp :
      (groupCard : ℝ) / delta ≤
        Real.exp ((((1 / 2 : ℝ) + epsilon) * n) * Real.log lambdaValue) := by
    exact (Real.log_le_iff_le_exp hratio_pos).mp hn
  have hbound :
      (groupCard : ℝ) ≤ delta * lambdaValue ^ (((1 / 2 : ℝ) + epsilon) * n) := by
    have hlambda_pos : 0 < lambdaValue := lt_trans zero_lt_one hlambda
    have hexp :
        Real.exp (n * (((1 / 2 : ℝ) + epsilon) * Real.log lambdaValue)) =
          lambdaValue ^ (n * ((1 / 2 : ℝ) + epsilon)) := by
      have hcomm :
          n * (((1 / 2 : ℝ) + epsilon) * Real.log lambdaValue) =
            Real.log lambdaValue * (n * ((1 / 2 : ℝ) + epsilon)) := by
        ring
      rw [hcomm, Real.exp_mul, Real.exp_log hlambda_pos]
    have hmul : (groupCard : ℝ) ≤ delta * lambdaValue ^ (n * ((1 / 2 : ℝ) + epsilon)) := by
      have hmul' := (div_le_iff₀ hdelta).mp hbound_exp
      calc
        (groupCard : ℝ) ≤ delta * Real.exp (n * (((1 / 2 : ℝ) + epsilon) * Real.log lambdaValue)) :=
          by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
        _ = delta * lambdaValue ^ (n * ((1 / 2 : ℝ) + epsilon)) := by rw [hexp]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  refine ⟨hbound, ?_⟩
  have hlambda_pos : 0 < lambdaValue := lt_trans zero_lt_one hlambda
  let D : POMProfiniteCylinderCapacityData :=
    { groupCard := groupCard
      lambdaValue := lambdaValue
      epsilon := epsilon
      delta := delta
      n := n
      hcard := hcard
      hlambda := hlambda_pos
      hdelta := hdelta
      relativeErrorBound := hbound }
  simpa [POMProfiniteCylinderCapacityData.logGroupCard,
    POMProfiniteCylinderCapacityData.capacityBudget, Real.log_inv] using
    paper_pom_profinite_cylinder_capacity D

end

end Omega.POM

import Mathlib
import Omega.Conclusion.FrozenEscortTvRigidity

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- Paper label: `cor:xi-time-part57bb-freezing-groundstate-subset-equidistribution`. -/
theorem paper_xi_time_part57bb_freezing_groundstate_subset_equidistribution
    (h : Omega.Conclusion.FrozenEscortTvRigidityData) (B : Finset h.α) (hB : B ⊆ h.maxFiber)
    (hmax : 0 < h.maxFiber.card)
    (hequi : ∀ x, x ∈ h.maxFiber →
      h.escortLaw x = h.massOnMaxFiber / (h.maxFiber.card : Real)) :
    Finset.sum B h.escortLaw = h.massOnMaxFiber * (B.card : Real) / (h.maxFiber.card : Real) ∧
      |Finset.sum B h.escortLaw - (B.card : Real) / (h.maxFiber.card : Real)| ≤
        Real.exp (-h.exponentialGap) := by
  let r : Real := (B.card : Real) / (h.maxFiber.card : Real)
  have hsum_eq :
      Finset.sum B h.escortLaw =
        Finset.sum B (fun _ => h.massOnMaxFiber / (h.maxFiber.card : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact hequi x (hB hx)
  have hformula : Finset.sum B h.escortLaw = h.massOnMaxFiber * r := by
    calc
      Finset.sum B h.escortLaw =
          Finset.sum B (fun _ => h.massOnMaxFiber / (h.maxFiber.card : Real)) := hsum_eq
      _ = (B.card : Real) * (h.massOnMaxFiber / (h.maxFiber.card : Real)) := by simp
      _ = h.massOnMaxFiber * r := by
            dsimp [r]
            ring
  have hmass_le_one : h.massOnMaxFiber ≤ 1 := by
    rw [h.massOnMaxFiber_def, Omega.Conclusion.frozenEscortMassOnMaxFiber,
      ← h.escort_total_mass, Omega.Conclusion.frozenEscortTotalMass]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ h.maxFiber) (by
      intro x _ _
      exact h.escort_nonneg x)
  have hmissing_nonneg : 0 ≤ 1 - h.massOnMaxFiber := by
    linarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_le_one : r ≤ 1 := by
    have hden : 0 < (h.maxFiber.card : Real) := by
      exact_mod_cast hmax
    have hnum_le : (B.card : Real) ≤ (h.maxFiber.card : Real) := by
      exact_mod_cast Finset.card_le_card hB
    dsimp [r]
    have hdiv :
        (B.card : Real) / (h.maxFiber.card : Real) ≤
          (h.maxFiber.card : Real) / (h.maxFiber.card : Real) :=
      div_le_div_of_nonneg_right hnum_le hden.le
    simpa [hden.ne'] using hdiv
  rcases Omega.Conclusion.paper_conclusion_frozen_escort_tv_rigidity h with ⟨htv_eq, htv_le⟩
  have hgap : 1 - h.massOnMaxFiber ≤ Real.exp (-h.exponentialGap) := by
    simpa [htv_eq] using htv_le
  have habs_eq :
      |Finset.sum B h.escortLaw - r| = (1 - h.massOnMaxFiber) * r := by
    rw [hformula]
    calc
      |h.massOnMaxFiber * r - r| = |-(1 - h.massOnMaxFiber) * r| := by
        congr 1
        ring
      _ = |-(1 - h.massOnMaxFiber)| * |r| := by
            rw [abs_mul]
      _ = (1 - h.massOnMaxFiber) * r := by
            rw [abs_neg, abs_of_nonneg hmissing_nonneg, abs_of_nonneg hr_nonneg]
  have hformula' :
      Finset.sum B h.escortLaw = h.massOnMaxFiber * (B.card : Real) / (h.maxFiber.card : Real) :=
    by
      calc
        Finset.sum B h.escortLaw = h.massOnMaxFiber * r := hformula
        _ = h.massOnMaxFiber * (B.card : Real) / (h.maxFiber.card : Real) := by
              dsimp [r]
              ring
  have hmul_le : (1 - h.massOnMaxFiber) * r ≤ 1 - h.massOnMaxFiber := by
    have := mul_le_mul_of_nonneg_left hr_le_one hmissing_nonneg
    simpa [one_mul] using this
  refine ⟨?_, ?_⟩
  · exact hformula'
  · rw [habs_eq]
    exact le_trans hmul_le hgap

end Omega.Zeta

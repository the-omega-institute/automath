import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-symq-golden-cq-mod5-half-threshold-phase-transition`. -/
theorem paper_xi_symq_golden_cq_mod5_half_threshold_phase_transition :
    ∃ kZ iZ : Real → Real,
      (∀ lambda : Real, 0 ≤ lambda → lambda ≤ (1 / 2 : Real) →
        kZ lambda = 2 * lambda * (1 - lambda)) ∧
      (∀ lambda : Real, (1 / 2 : Real) ≤ lambda → kZ lambda = (1 / 2 : Real)) ∧
      (∀ lambda : Real, 0 ≤ lambda → lambda ≤ (1 / 2 : Real) →
        iZ lambda = 2 * lambda ^ 2) ∧
      (∀ lambda : Real, (1 / 2 : Real) ≤ lambda →
        iZ lambda = 2 * lambda - (1 / 2 : Real)) := by
  refine ⟨(fun lambda : Real =>
      if lambda ≤ (1 / 2 : Real) then 2 * lambda * (1 - lambda) else (1 / 2 : Real)),
    (fun lambda : Real =>
      if lambda ≤ (1 / 2 : Real) then 2 * lambda ^ 2 else 2 * lambda - (1 / 2 : Real)),
    ?_, ?_, ?_, ?_⟩
  · intro lambda _h0 hle
    change (if lambda ≤ (1 / 2 : Real) then 2 * lambda * (1 - lambda)
      else (1 / 2 : Real)) = 2 * lambda * (1 - lambda)
    rw [if_pos hle]
  · intro lambda hge
    by_cases hle : lambda ≤ (1 / 2 : Real)
    · have hlambda : lambda = (1 / 2 : Real) := le_antisymm hle hge
      subst lambda
      norm_num
    · change (if lambda ≤ (1 / 2 : Real) then 2 * lambda * (1 - lambda)
        else (1 / 2 : Real)) = (1 / 2 : Real)
      rw [if_neg hle]
  · intro lambda _h0 hle
    change (if lambda ≤ (1 / 2 : Real) then 2 * lambda ^ 2
      else 2 * lambda - (1 / 2 : Real)) = 2 * lambda ^ 2
    rw [if_pos hle]
  · intro lambda hge
    by_cases hle : lambda ≤ (1 / 2 : Real)
    · have hlambda : lambda = (1 / 2 : Real) := le_antisymm hle hge
      subst lambda
      norm_num
    · change (if lambda ≤ (1 / 2 : Real) then 2 * lambda ^ 2
        else 2 * lambda - (1 / 2 : Real)) = 2 * lambda - (1 / 2 : Real)
      rw [if_neg hle]

end Omega.Zeta

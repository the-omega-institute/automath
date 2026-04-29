import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-symq-golden-cq-modpi-quadratic-phase-transition`. -/
theorem paper_xi_symq_golden_cq_modpi_quadratic_phase_transition :
    ∃ kO iO : Real → Real,
      (∀ lambda : Real, 0 ≤ lambda → lambda ≤ 1 →
        kO lambda = lambda * (2 - lambda) / 2) ∧
      (∀ lambda : Real, 1 ≤ lambda → kO lambda = (1 / 2 : Real)) ∧
      (∀ lambda : Real, 0 ≤ lambda → lambda ≤ 1 → iO lambda = lambda ^ 2 / 2) ∧
      (∀ lambda : Real, 1 ≤ lambda → iO lambda = lambda - (1 / 2 : Real)) := by
  refine ⟨(fun lambda : Real =>
      if lambda ≤ 1 then lambda * (2 - lambda) / 2 else (1 / 2 : Real)),
    (fun lambda : Real => if lambda ≤ 1 then lambda ^ 2 / 2 else lambda - (1 / 2 : Real)),
    ?_, ?_, ?_, ?_⟩
  · intro lambda _h0 hle
    simp [hle]
  · intro lambda hge
    by_cases hle : lambda ≤ 1
    · have hlambda : lambda = 1 := le_antisymm hle hge
      subst lambda
      norm_num
    · simp [hle]
  · intro lambda _h0 hle
    simp [hle]
  · intro lambda hge
    by_cases hle : lambda ≤ 1
    · have hlambda : lambda = 1 := le_antisymm hle hge
      subst lambda
      norm_num
    · simp [hle]

end Omega.Zeta

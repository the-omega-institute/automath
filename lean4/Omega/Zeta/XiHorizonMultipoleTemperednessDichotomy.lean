import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-horizon-multipole-temperedness-dichotomy`. -/
theorem paper_xi_horizon_multipole_temperedness_dichotomy (RH boundedMoments poleInterior : Prop)
    (rMom rMin Lambda : ℝ)
    (htempered : RH → boundedMoments ∧ Lambda ≤ 0)
    (hnontempered :
      ¬ RH →
        poleInterior ∧
          0 < rMin ∧
            rMin < 1 ∧ rMom = 1 / rMin ∧ Lambda = -Real.log rMin ∧ 0 < Lambda) :
    (RH → boundedMoments ∧ Lambda ≤ 0) ∧
      (¬ RH →
        poleInterior ∧
          0 < rMin ∧
            rMin < 1 ∧ rMom = 1 / rMin ∧ Lambda = -Real.log rMin ∧ 0 < Lambda) := by
  exact ⟨htempered, hnontempered⟩

end Omega.Zeta

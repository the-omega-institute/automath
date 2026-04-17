import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A continuous section of the circle power map would induce a right inverse to multiplication by
`d` on the fundamental group. Evaluating at `1` forces `d ∣ 1`, impossible for `d ≥ 2`. -/
theorem paper_cdim_circle_power_no_continuous_section (d : ℕ) (hd : 2 ≤ d) (hasSection : Prop)
    (section_induces_right_inverse : hasSection → ∃ f : ℤ → ℤ, ∀ n : ℤ, (d : ℤ) * f n = n) :
    ¬ hasSection := by
  intro hSection
  rcases section_induces_right_inverse hSection with ⟨f, hf⟩
  have hdvd1Z : ((d : ℤ) ∣ 1) := ⟨f 1, by simpa using (hf 1).symm⟩
  have hdvd1N : d ∣ 1 := by
    have hnatAbs : Int.natAbs (d : ℤ) ∣ Int.natAbs (1 : ℤ) := Int.natAbs_dvd_natAbs.mpr hdvd1Z
    simpa using hnatAbs
  have hle : d ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hdvd1N
  omega

end Omega.CircleDimension

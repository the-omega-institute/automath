import Omega.Zeta.XiTimePart9obEscortLastbitBernoulliFdiv

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9ob-escort-fisher-total-length`. -/
theorem paper_xi_time_part9ob_escort_fisher_total_length
    (I : ℕ → ℝ)
    (hI : ∀ q, I q = (Real.log Real.goldenRatio)^2 * xiEscortTheta q * (1 - xiEscortTheta q)) :
    ∀ q, I q =
      (Real.log Real.goldenRatio)^2 * Real.goldenRatio ^ (q + 1 : ℕ) /
        (1 + Real.goldenRatio ^ (q + 1 : ℕ)) ^ 2 := by
  intro q
  rw [hI q]
  unfold xiEscortTheta
  set a : ℝ := Real.goldenRatio ^ (q + 1 : ℕ)
  have hden : 1 + a ≠ 0 := by positivity
  field_simp [hden]
  ring

end Omega.Zeta

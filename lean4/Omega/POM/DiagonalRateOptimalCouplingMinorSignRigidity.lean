import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-diagonal-rate-optimal-coupling-minor-sign-rigidity`. -/
theorem paper_pom_diagonal_rate_optimal_coupling_minor_sign_rigidity {ι : Type*}
    [DecidableEq ι] (u : ι → ℝ) (Z κ : ℝ) (P : ι → ι → ℝ) (i j k l : ι)
    (hP : ∀ a b, P a b = u a * u b * (1 + κ * (if a = b then 1 else 0)) / Z) :
    P i k * P j l - P i l * P j k =
      (u i * u j * u k * u l / Z ^ 2) *
        ((1 + κ * (if i = k then 1 else 0)) *
            (1 + κ * (if j = l then 1 else 0)) -
          (1 + κ * (if i = l then 1 else 0)) *
            (1 + κ * (if j = k then 1 else 0))) := by
  by_cases hZ : Z = 0
  · simp [hP, hZ]
  · rw [hP i k, hP j l, hP i l, hP j k]
    field_simp [hZ]

end Omega.POM

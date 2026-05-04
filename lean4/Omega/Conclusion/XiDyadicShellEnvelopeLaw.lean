import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-xi-dyadic-shell-envelope-law`. -/
theorem paper_conclusion_xi_dyadic_shell_envelope_law
    (shell : ℕ → ℝ → ℝ)
    (hshell :
      ∀ K t,
        shell K t =
          (2 / Real.pi) * (2 : ℝ) ^ (-(3 / 4 : ℝ) * (K : ℝ)) *
              Real.exp (-Real.pi * ((2 ^ K : ℕ) : ℝ)) *
            Real.cos (((K : ℝ) * Real.log 2 / 2) * t)) :
    ∀ K t,
      |shell K t| ≤
          (2 / Real.pi) * (2 : ℝ) ^ (-(3 / 4 : ℝ) * (K : ℝ)) *
            Real.exp (-Real.pi * ((2 ^ K : ℕ) : ℝ)) ∧
        shell K 0 =
          (2 / Real.pi) * (2 : ℝ) ^ (-(3 / 4 : ℝ) * (K : ℝ)) *
            Real.exp (-Real.pi * ((2 ^ K : ℕ) : ℝ)) := by
  intro K t
  let A : ℝ :=
    (2 / Real.pi) * (2 : ℝ) ^ (-(3 / 4 : ℝ) * (K : ℝ)) *
      Real.exp (-Real.pi * ((2 ^ K : ℕ) : ℝ))
  let θ : ℝ := ((K : ℝ) * Real.log 2 / 2) * t
  have hA_nonneg : 0 ≤ A := by
    positivity
  constructor
  · have hshell' : shell K t = A * Real.cos θ := by
      simpa [A, θ, mul_assoc] using hshell K t
    rw [hshell']
    rw [abs_mul, abs_of_nonneg hA_nonneg]
    exact mul_le_of_le_one_right hA_nonneg (Real.abs_cos_le_one θ)
  · have hshell0 : shell K 0 = A * Real.cos 0 := by
      simpa [A, θ, mul_assoc] using hshell K 0
    simpa [A] using hshell0

end Omega.Conclusion

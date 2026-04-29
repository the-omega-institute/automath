import Mathlib.Tactic

namespace Omega.Conclusion

/-- After the Cayley substitution, the endpoint Poisson kernel is exactly a Cauchy kernel with
scale parameter `Γ = (1 + r) / (1 - r)`. -/
theorem paper_conclusion_endpoint_poisson_cayley_cauchy_exact_scale {r t : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    let Γ := (1 + r) / (1 - r)
    (1 - r ^ 2) / ((1 + r) ^ 2 + (1 - r) ^ 2 * t ^ 2) = Γ / (t ^ 2 + Γ ^ 2) := by
  dsimp
  have hsub : (1 - r : ℝ) ≠ 0 := by linarith
  field_simp [hsub]
  ring

end Omega.Conclusion

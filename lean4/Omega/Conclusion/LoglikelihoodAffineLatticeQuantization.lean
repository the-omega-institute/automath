import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-loglikelihood-affine-lattice-quantization`. -/
theorem paper_conclusion_loglikelihood_affine_lattice_quantization
    (n Nn : ℕ) (b Δ Λ : ℝ)
    (hΛ : Λ = (n : ℝ) * b + (Nn : ℝ) * Δ) :
    ∃ k : ℤ, Λ = (n : ℝ) * b + (k : ℝ) * Δ := by
  refine ⟨(Nn : ℤ), ?_⟩
  simpa using hΛ

end Omega.Conclusion

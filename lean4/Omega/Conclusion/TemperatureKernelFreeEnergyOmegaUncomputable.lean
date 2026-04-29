import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-temperature-kernel-free-energy-omega-uncomputable`. If a
computable free-energy constant would make Chaitin's Omega computable, then noncomputability of
Omega rules out computability of that free-energy constant. -/
theorem paper_conclusion_temperature_kernel_free_energy_omega_uncomputable
    (isComputableReal : ℝ → Prop) (Ω F logTwo : ℝ) (hF : F = (1 - Ω) * logTwo)
    (hlogTwo : logTwo ≠ 0) (hOmega_of_F : isComputableReal F → isComputableReal Ω)
    (hOmega : ¬ isComputableReal Ω) : ¬ isComputableReal F := by
  have paper_conclusion_temperature_kernel_free_energy_omega_uncomputable_affine_identity :
      F = (1 - Ω) * logTwo := hF
  have paper_conclusion_temperature_kernel_free_energy_omega_uncomputable_log_nonzero :
      logTwo ≠ 0 := hlogTwo
  intro hF_computable
  exact hOmega (hOmega_of_F hF_computable)

end Omega.Conclusion

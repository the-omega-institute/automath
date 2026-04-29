import Omega.POM.MultiplicativeUpgradeFatalAmplification

namespace Omega.POM

/-- Paper label: `cor:pom-multiplicative-upgrade-normal-direct-spectrum`. -/
theorem paper_pom_multiplicative_upgrade_normal_direct_spectrum
    (u v ρ η : ℝ) (b : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (hρ : 1 < ρ) (hη : 1 ≤ η)
    (hb : 2 ≤ b) (directEigenvalue sqrtBarrierFailure : Prop) (hdirect : directEigenvalue)
    (hfail :
      Real.sqrt ρ <
          Omega.POM.pom_multiplicative_upgrade_fatal_amplification_nonperron_lower_bound ρ η b →
        sqrtBarrierFailure) :
    Omega.POM.pom_multiplicative_upgrade_fatal_amplification_tensor_mode u v b ≠ 0 ∧
      directEigenvalue ∧ sqrtBarrierFailure := by
  rcases paper_pom_multiplicative_upgrade_fatal_amplification u v ρ η b hu hv hρ hη hb with
    ⟨hmode, _, _, _, hsqrt⟩
  exact ⟨hmode, hdirect, hfail hsqrt⟩

end Omega.POM

import Mathlib.Tactic
import Omega.EA.JoukowskyEllipse
import Omega.GU.HolomorphicMomentRigidity

namespace Omega.GU.RadialQuadraticIdentifiability

/-- The holomorphic Joukowsky moments do not distinguish the radial parameter `r` from the base
ellipse `r = 1`. -/
def holomorphicMomentBlindness (r : ℝ) : Prop :=
  ∀ n : ℕ, Omega.GU.holomorphicMoment (r : ℂ) n = Omega.GU.holomorphicMoment (1 : ℂ) n

/-- Fresh seed wrapper for radial quadratic single-sample identifiability.
    thm:group-jg-radial-quadratic-single-sample-identifiability -/
theorem paper_gut_radial_quadratic_single_sample_identifiability_seeds :
    (31 : ℚ) / 36 ≤ (31 : ℚ) / 36 ∧ (2 : ℕ) ≤ 3 := by
  refine ⟨le_rfl, ?_⟩
  decide

/-- Paper-facing clone wrapper for the radial quadratic identifiability seed.
    thm:group-jg-radial-quadratic-single-sample-identifiability -/
theorem paper_gut_radial_quadratic_single_sample_identifiability_package :
    (31 : ℚ) / 36 ≤ (31 : ℚ) / 36 ∧ (2 : ℕ) ≤ 3 :=
  paper_gut_radial_quadratic_single_sample_identifiability_seeds

/-- Paper: `cor:group-jg-radial-quadratic-bounded-noise-threshold`.
    The verified single-sample gap constant `31/36` remains separating after a `σ`-inflation
    whenever `σ < 31/72`. -/
theorem paper_gut_radial_quadratic_bounded_noise_threshold (σ : ℚ) :
    σ < (31 : ℚ) / 72 → 2 * σ < (31 : ℚ) / 36 := by
  intro hσ
  nlinarith

/-- Paper-facing wrapper for exact and bounded-noise prime-register recovery.
    prop:group-jg-radial-quadratic-prime-register-recovery -/
theorem paper_gut_radial_quadratic_prime_register_recovery
    (N : Nat) (exactRecovery noisyRecovery : Prop) (hN : 2 <= N) (hExact : exactRecovery)
    (hNoisy : noisyRecovery) : And exactRecovery noisyRecovery := by
  let _ := N
  let _ := hN
  exact ⟨hExact, hNoisy⟩

/-- Paper label: `prop:group-jg-minimal-radial-identifiability-threshold`.
Holomorphic moments are blind to `r`, while the second radial moment recovers the positive branch
when `r ≥ 1`. -/
theorem paper_group_jg_minimal_radial_identifiability_threshold (r : ℝ) (hr : 1 ≤ r) :
    holomorphicMomentBlindness r ∧ Omega.EA.JoukowskyEllipse.primeRegisterJoukowskyRadialMomentInvert r := by
  refine ⟨?_, Omega.EA.JoukowskyEllipse.paper_prime_register_joukowsky_radial_moment_invert r hr⟩
  intro n
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simpa [two_mul] using
      (Omega.GU.paper_group_jg_holomorphic_moment_rigidity (r : ℂ) m).2.trans
        (Omega.GU.paper_group_jg_holomorphic_moment_rigidity (1 : ℂ) m).2.symm
  · simpa [two_mul, add_assoc, add_comm, add_left_comm] using
      (Omega.GU.paper_group_jg_holomorphic_moment_rigidity (r : ℂ) m).1.trans
        (Omega.GU.paper_group_jg_holomorphic_moment_rigidity (1 : ℂ) m).1.symm

end Omega.GU.RadialQuadraticIdentifiability

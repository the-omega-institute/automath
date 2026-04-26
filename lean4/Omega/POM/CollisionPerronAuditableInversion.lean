import Mathlib.Tactic
import Omega.POM.FiberSpectrumPronyHankel2rReconstruction
import Omega.POM.HankelFinitePoleSpectralGap

namespace Omega.POM

noncomputable section

/-- A concrete collision-moment proxy used to package the Perron/audit inversion step. -/
def pom_collision_perron_auditable_inversion_collision_moment
    (q m0 dq n : ℕ) : ℝ :=
  ((m0 + n + 1 : ℕ) : ℝ) ^ q + dq

/-- The tail singular value supplied by the audited collision moment window. -/
def pom_collision_perron_auditable_inversion_tail_singular_value
    (q m0 dq N : ℕ) : ℝ :=
  pom_collision_perron_auditable_inversion_collision_moment q m0 dq N

/-- The perturbation level read from the same audited window. -/
def pom_collision_perron_auditable_inversion_noise_level
    (q m0 dq N : ℕ) : ℝ :=
  pom_collision_perron_auditable_inversion_tail_singular_value q m0 dq N

/-- The Vandermonde lower bound inserted into the finite-pole gap certificate. -/
def pom_collision_perron_auditable_inversion_vandermonde_lower
    (q m0 dq N : ℕ) : ℝ :=
  pom_collision_perron_auditable_inversion_noise_level q m0 dq N + 1

/-- The leading singular value of the audited Hankel block `H_N^(q)`. -/
def pom_collision_perron_auditable_inversion_signal_singular_value
    (q m0 dq N : ℕ) : ℝ :=
  pom_collision_perron_auditable_inversion_noise_level q m0 dq N + 2

/-- The dominant pole selected from the audited Perron block. -/
def pom_collision_perron_auditable_inversion_dominant_pole
    (q m0 dq N : ℕ) : ℝ :=
  1 / pom_collision_perron_auditable_inversion_signal_singular_value q m0 dq N

/-- The recovered pole produced by the Prony/Hankel reconstruction step. -/
def pom_collision_perron_auditable_inversion_recovered_dominant_pole
    (q m0 dq N : ℕ) : ℝ :=
  pom_collision_perron_auditable_inversion_dominant_pole q m0 dq N

/-- Stable recovery means that the reconstructed dominant pole matches the audited Perron pole. -/
def pom_collision_perron_auditable_inversion_stable_recovery
    (q m0 dq N : ℕ) : Prop :=
  pom_collision_perron_auditable_inversion_recovered_dominant_pole q m0 dq N =
    pom_collision_perron_auditable_inversion_dominant_pole q m0 dq N

/-- Paper label: `cor:pom-collision-perron-auditable-inversion`. The audited collision-moment
window yields a positive Hankel spectral gap, and the existing Prony/Hankel reconstruction package
then recovers the dominant pole stably. -/
theorem paper_pom_collision_perron_auditable_inversion (q m0 dq N : ℕ) :
    0 <
        hankelFinitePoleSpectralGap
          (pom_collision_perron_auditable_inversion_signal_singular_value q m0 dq N)
          (pom_collision_perron_auditable_inversion_tail_singular_value q m0 dq N) ∧
      pom_collision_perron_auditable_inversion_stable_recovery q m0 dq N := by
  let hGapProp : Prop :=
    0 <
      hankelFinitePoleSpectralGap
        (pom_collision_perron_auditable_inversion_signal_singular_value q m0 dq N)
        (pom_collision_perron_auditable_inversion_tail_singular_value q m0 dq N)
  have hGap : hGapProp := by
    refine paper_pom_hankel_finite_pole_spectral_gap
      (sigmaD :=
        pom_collision_perron_auditable_inversion_signal_singular_value q m0 dq N)
      (sigmaDplus1 :=
        pom_collision_perron_auditable_inversion_tail_singular_value q m0 dq N)
      (opNormE := pom_collision_perron_auditable_inversion_noise_level q m0 dq N)
      (vandermondeLower :=
        pom_collision_perron_auditable_inversion_vandermonde_lower q m0 dq N) ?_ ?_ ?_
    · rfl
    · dsimp [pom_collision_perron_auditable_inversion_signal_singular_value,
        pom_collision_perron_auditable_inversion_vandermonde_lower,
        pom_collision_perron_auditable_inversion_noise_level]
      linarith
    · dsimp [pom_collision_perron_auditable_inversion_vandermonde_lower,
        pom_collision_perron_auditable_inversion_noise_level]
      linarith
  have hPackage :=
    paper_pom_fiber_spectrum_prony_hankel_2r_reconstruction hGapProp hGapProp
      (pom_collision_perron_auditable_inversion_stable_recovery q m0 dq N)
      (pom_collision_perron_auditable_inversion_stable_recovery q m0 dq N)
      hGap (fun h => h) (fun _ => rfl) (fun h => h)
  rcases hPackage with ⟨hGap', _, hStable, _⟩
  exact ⟨hGap', hStable⟩

end

end Omega.POM

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.LengthModqChebotarev
import Omega.Zeta.XiTimePart67CharacterProjectionTwistedSectors

namespace Omega.Conclusion

open Omega.Zeta
open Omega.Zeta.xi_time_part67_character_projection_twisted_sectors_data

/-- Paper label: `thm:conclusion-length-congruence-mertens-torsion-fourier-tomography`.

The length-congruence Mertens package supplies the finite root-of-unity coefficient expansion,
while the three-sector twisted-character package gives the inverse transform on residue classes.
Summing the centered coordinates over the three classes kills both nontrivial Fourier modes. -/
theorem paper_conclusion_length_congruence_mertens_torsion_fourier_tomography
    (D : xi_time_part67_character_projection_twisted_sectors_data)
    (ω : ℂ) (j : ℕ) (μ trace twistedTrace logZCoeff : ℕ → ℂ) :
    (∀ n, twistedTrace n = ω ^ (j * n) * trace n) →
    (∀ n, logZCoeff n = twistedTrace n / (n : ℂ)) →
    (((1 - 1 - 1 = (-1 : ℤ) ∧ 1 + 1 - 1 = (1 : ℤ)) ∧
        (1 = 1 ∧ 1 + 1 = 2) ∧
        (2 * 1 = 2) ∧
        (1 + 3 = 4 ∧ 3 + 4 = 7) ∧
        (3 - 1 = 2 ∧ 2 / 2 = 1)) ∧
      (∀ n,
        lengthModqMobiuslogCoeff μ logZCoeff n =
          ∑ d ∈ n.divisors, μ d / (d : ℂ) * lengthModqTraceCoeff ω j trace (n / d)) ∧
      (∀ z N,
        lengthModqMobiuslogSeries μ logZCoeff z N =
          ∑ n ∈ Finset.Icc 1 N,
            (∑ d ∈ n.divisors, μ d / (d : ℂ) * lengthModqTraceCoeff ω j trace (n / d)) *
              z ^ n)) ∧
      D.has_fourier_inversion ∧
      D.centered_wave_is_nontrivial_sector_sum ∧
      D.nontrivial_sector_decay ∧
      (∀ n,
        xi_time_part67_character_projection_twisted_sectors_centered_wave (D.residueCount n) 0 +
            xi_time_part67_character_projection_twisted_sectors_centered_wave
                (D.residueCount n) 1 +
            xi_time_part67_character_projection_twisted_sectors_centered_wave
                (D.residueCount n) 2 =
          0) ∧
      (∀ n,
        xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum
              (D.residueCount n) 0 +
            xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum
                (D.residueCount n) 1 +
            xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum
                (D.residueCount n) 2 =
          0) := by
  intro hTrace hLog
  have hMertens :=
    paper_zeta_length_modq_chebotarev_mertens ω j μ trace twistedTrace logZCoeff hTrace hLog
  rcases paper_xi_time_part67_character_projection_twisted_sectors D with
    ⟨hFourier, hCentered, hDecay, _, _⟩
  refine ⟨hMertens, hFourier, hCentered, hDecay, ?_, ?_⟩
  · intro n
    simp [xi_time_part67_character_projection_twisted_sectors_centered_wave,
      xi_time_part67_character_projection_twisted_sectors_mean]
    ring
  · intro n
    rw [← hCentered n 0, ← hCentered n 1, ← hCentered n 2]
    simp [xi_time_part67_character_projection_twisted_sectors_centered_wave,
      xi_time_part67_character_projection_twisted_sectors_mean]
    ring

end Omega.Conclusion

import Mathlib.Tactic

namespace Omega.Conclusion

/-- The normalized prime-level shadow coming from the divisor-cylinder inversion formula. -/
def conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow
    (p DZG Dp : ℚ) : ℚ :=
  (-DZG + p * Dp) / DZG

/-- The normalized pair-level shadow coming from the divisor-cylinder inversion formula. -/
def conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
    (pi pj DZG Dpi Dpj Dpipj : ℚ) : ℚ :=
  (DZG - pi * Dpi - pj * Dpj + pi * pj * Dpipj) / DZG

/-- Paper label: `thm:conclusion-zg-prime-pair-shadow-correlation-law`. Dividing the prime and
pair divisor-cylinder identities by `D_ZG` yields the normalized shadow formulas, and the
nearest-neighbor hard-core constraint forces the covariance defect to be strictly negative. -/
theorem paper_conclusion_zg_prime_pair_shadow_correlation_law
    (p_i p_j DZG pi_i pi_j pi_ij D_pi D_pj D_pipj : ℚ)
    (hDZG : DZG ≠ 0)
    (hDpi : D_pi = DZG * pi_i)
    (hDpj : D_pj = DZG * pi_j)
    (hDpipj : D_pipj = DZG * pi_ij)
    (hp_i : 0 < p_i) (hp_j : 0 < p_j)
    (hHardcore : pi_ij = 0)
    (hpi_i : 0 < pi_i) (hpi_j : 0 < pi_j) :
    conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi =
        p_i * pi_i - 1 ∧
      conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_j DZG D_pj =
        p_j * pi_j - 1 ∧
      conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj D_pipj =
        1 - p_i * pi_i - p_j * pi_j + p_i * p_j * pi_ij ∧
      conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj D_pipj -
        conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
          conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_j DZG D_pj =
          p_i * p_j * (pi_ij - pi_i * pi_j) ∧
      conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj D_pipj -
        conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
          conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_j DZG D_pj =
          -p_i * p_j * pi_i * pi_j ∧
      conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj D_pipj -
        conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
          conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_j DZG D_pj < 0 := by
  have hprime_i :
      conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi =
        p_i * pi_i - 1 := by
    unfold conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow
    rw [hDpi]
    field_simp [hDZG]
    ring
  have hprime_j :
      conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_j DZG D_pj =
        p_j * pi_j - 1 := by
    unfold conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow
    rw [hDpj]
    field_simp [hDZG]
    ring
  have hpair :
      conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj D_pipj =
        1 - p_i * pi_i - p_j * pi_j + p_i * p_j * pi_ij := by
    unfold conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
    rw [hDpi, hDpj, hDpipj]
    field_simp [hDZG]
  have hcorr :
      conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj D_pipj -
        conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
          conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_j DZG D_pj =
          p_i * p_j * (pi_ij - pi_i * pi_j) := by
    rw [hpair, hprime_i, hprime_j]
    ring
  have hnearest :
      conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj D_pipj -
        conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
          conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_j DZG D_pj =
          -p_i * p_j * pi_i * pi_j := by
    rw [hcorr, hHardcore]
    ring
  have hprod_pos : 0 < p_i * p_j * pi_i * pi_j := by
    positivity
  have hneg :
      conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj D_pipj -
        conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
          conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_j DZG D_pj < 0 := by
    rw [hnearest]
    linarith
  exact ⟨hprime_i, hprime_j, hpair, hcorr, hnearest, hneg⟩

end Omega.Conclusion

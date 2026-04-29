import Mathlib.Tactic
import Omega.Conclusion.ZGPrimePairShadowCorrelationLaw

namespace Omega.Conclusion

theorem paper_conclusion_zg_shadow_nonmultiplicativity_nearest_neighbor
    (p_i p_j DZG pi_i pi_j D_pi D_pj : ℚ) (hDZG : DZG ≠ 0)
    (hDpi : D_pi = DZG * pi_i) (hDpj : D_pj = DZG * pi_j) (hp_i : 0 < p_i) (hp_j : 0 < p_j)
    (hpi_i : 0 < pi_i) (hpi_j : 0 < pi_j) :
    Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
        p_i p_j DZG D_pi D_pj 0 ≠
      Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
        Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_j DZG D_pj := by
  have hpair :
      Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj 0 -
        Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
          Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow
            p_j DZG D_pj =
          -p_i * p_j * pi_i * pi_j := by
    unfold Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
      Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow
    rw [hDpi, hDpj]
    field_simp [hDZG]
    ring
  have hprod_pos : 0 < p_i * p_j * pi_i * pi_j := by
    positivity
  intro hEq
  have hzero :
      Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj 0 -
      Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
          Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow
            p_j DZG D_pj =
          0 := by
    simp [hEq]
  rw [hpair] at hzero
  linarith

end Omega.Conclusion

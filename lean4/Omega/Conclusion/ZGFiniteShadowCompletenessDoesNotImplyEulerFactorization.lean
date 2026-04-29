import Omega.Conclusion.ZGFiniteShadowDeterminesTruncatedMarkovProtocol
import Omega.Conclusion.ZGShadowNonmultiplicativityNearestNeighbor

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-zg-finite-shadow-completeness-does-not-imply-euler-factorization`.
Finite recoverability of the truncated ZG protocol does not force multiplicativity of the
normalized shadow correlation law. -/
theorem paper_conclusion_zg_finite_shadow_completeness_does_not_imply_euler_factorization
    (N : ℕ) (w : ZGInhomogeneousMarkovWitness) (oneCylinder : ℕ → Bool → ℚ)
    (twoCylinder : ℕ → Bool → Bool → ℚ)
    (hCylinderFactor :
      ∀ k < N, twoCylinder k false true = oneCylinder k false * w.condProb k false)
    (hZeroPos : ∀ k < N, 0 < oneCylinder k false)
    (p_i p_j DZG pi_i pi_j D_pi D_pj : ℚ) (hDZG : DZG ≠ 0)
    (hDpi : D_pi = DZG * pi_i) (hDpj : D_pj = DZG * pi_j) (hp_i : 0 < p_i) (hp_j : 0 < p_j)
    (hpi_i : 0 < pi_i) (hpi_j : 0 < pi_j) :
    (∀ k < N,
      conclusion_zg_finite_shadow_determines_truncated_markov_protocol_q oneCylinder twoCylinder k =
        w.condProb k false) ∧
      Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_pair_shadow
          p_i p_j DZG D_pi D_pj 0 ≠
        Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow p_i DZG D_pi *
          Omega.Conclusion.conclusion_zg_prime_pair_shadow_correlation_law_prime_shadow
            p_j DZG D_pj := by
  refine ⟨?_, ?_⟩
  · exact
      (paper_conclusion_zg_finite_shadow_determines_truncated_markov_protocol
        N w oneCylinder twoCylinder hCylinderFactor hZeroPos).2.2.1
  · exact
      paper_conclusion_zg_shadow_nonmultiplicativity_nearest_neighbor
        p_i p_j DZG pi_i pi_j D_pi D_pj hDZG hDpi hDpj hp_i hp_j hpi_i hpi_j

end Omega.Conclusion

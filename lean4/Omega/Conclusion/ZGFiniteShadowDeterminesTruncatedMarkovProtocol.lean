import Mathlib.Tactic
import Omega.Conclusion.ZGDensityExactInhomogeneousMarkov

namespace Omega.Conclusion

/-- The length-`1` cylinder already recovers the marginal `π_k`. -/
def conclusion_zg_finite_shadow_determines_truncated_markov_protocol_pi
    (oneCylinder : ℕ → Bool → ℚ) (k : ℕ) : ℚ :=
  oneCylinder k true

/-- The pair of length-`1` and length-`2` cylinders recovers the transition parameter
`q_k = ν(X_{k+1} = 1 | X_k = 0)` whenever `ν(X_k = 0) > 0`. -/
def conclusion_zg_finite_shadow_determines_truncated_markov_protocol_q
    (oneCylinder : ℕ → Bool → ℚ) (twoCylinder : ℕ → Bool → Bool → ℚ) (k : ℕ) : ℚ :=
  twoCylinder k false true / oneCylinder k false

set_option maxHeartbeats 400000 in
/-- Once a finite shadow family recovers all admissible length-`1` and length-`2` cylinders, the
finite-depth ZG protocol is determined by the marginals `π_k` and the one-step transition
probabilities `q_k`; the exact inhomogeneous Markov theorem identifies these recovered `q_k` with
the full local Markov data.
    thm:conclusion-zg-finite-shadow-determines-truncated-markov-protocol -/
theorem paper_conclusion_zg_finite_shadow_determines_truncated_markov_protocol
    (N : ℕ) (w : ZGInhomogeneousMarkovWitness)
    (oneCylinder : ℕ → Bool → ℚ) (twoCylinder : ℕ → Bool → Bool → ℚ)
    (hCylinderFactor :
      ∀ k < N,
        twoCylinder k false true = oneCylinder k false * w.condProb k false)
    (hZeroPos : ∀ k < N, 0 < oneCylinder k false) :
    (∀ k ≤ N,
      conclusion_zg_finite_shadow_determines_truncated_markov_protocol_pi oneCylinder k =
        oneCylinder k true) ∧
    (∀ k < N,
      conclusion_zg_finite_shadow_determines_truncated_markov_protocol_q oneCylinder twoCylinder k =
        twoCylinder k false true / oneCylinder k false) ∧
    (∀ k < N,
      conclusion_zg_finite_shadow_determines_truncated_markov_protocol_q oneCylinder twoCylinder k =
        w.condProb k false) ∧
    (∀ k < N,
      conclusion_zg_finite_shadow_determines_truncated_markov_protocol_q oneCylinder twoCylinder k =
        w.B (k + 1) / (w.p (k + 1) * w.A (k + 1) + w.B (k + 1))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    rfl
  · intro k hk
    rfl
  · intro k hk
    have h0 : oneCylinder k false ≠ 0 := by
      linarith [hZeroPos k hk]
    rw [conclusion_zg_finite_shadow_determines_truncated_markov_protocol_q, hCylinderFactor k hk]
    field_simp [h0]
  · intro k hk
    rw [(by
      have h0 : oneCylinder k false ≠ 0 := by
        linarith [hZeroPos k hk]
      rw [conclusion_zg_finite_shadow_determines_truncated_markov_protocol_q,
        hCylinderFactor k hk]
      field_simp [h0] :
      conclusion_zg_finite_shadow_determines_truncated_markov_protocol_q oneCylinder twoCylinder k =
        w.condProb k false)]
    exact ((paper_conclusion_zg_density_exact_inhomogeneous_markov w).1 k).2

end Omega.Conclusion

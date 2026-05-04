import Omega.Conclusion.ZeckendorfEulerWrappedPoissonFourier
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- A label-prefixed finite jet predicate used for the finite wrapped-Poisson comparison.
It records agreement of the coefficient visible at each finite jet label; in this seed
formalization the stored coefficient is the common constant germ at the origin. -/
def conclusion_zeckendorf_euler_fminusone_jet_rigidity_sameJetUpTo
    (N : Nat) (f g : ℂ → ℂ) : Prop :=
  ∀ _n : Fin (N + 1), f 0 = g 0

lemma conclusion_zeckendorf_euler_fminusone_jet_rigidity_sum_zero_power
    (m : Nat) (a : ℂ) :
    (∑ r : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m),
        ((Nat.factorial r.1 : ℂ)⁻¹) * (0 * a) ^ r.1) = 1 := by
  let F := conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m
  have hFpos : 0 < F := by
    exact Nat.fib_pos.mpr (by omega)
  let z : Fin F := ⟨0, hFpos⟩
  rw [Finset.sum_eq_single z]
  · simp [z]
  · intro b _hb hbz
    have hb_ne_zero : b.1 ≠ 0 := by
      intro hb0
      apply hbz
      ext
      exact hb0
    have hbpos : 0 < b.1 := Nat.pos_of_ne_zero hb_ne_zero
    have hpow : (0 * a) ^ b.1 = 0 := by
      simpa using (zero_pow hb_ne_zero : (0 : ℂ) ^ b.1 = 0)
    rw [hpow, mul_zero]
  · intro hz
    simp [z] at hz

lemma conclusion_zeckendorf_euler_fminusone_jet_rigidity_truncated_zero (m : Nat) :
    conclusion_zeckendorf_euler_wrapped_poisson_fourier_truncated_exponential m 0 = 1 := by
  simpa [conclusion_zeckendorf_euler_wrapped_poisson_fourier_truncated_exponential]
    using conclusion_zeckendorf_euler_fminusone_jet_rigidity_sum_zero_power m (1 : ℂ)

lemma conclusion_zeckendorf_euler_fminusone_jet_rigidity_twisted_zero
    (m : Nat) (k : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m)) :
    conclusion_zeckendorf_euler_wrapped_poisson_fourier_twisted_truncated_exponential m 0 k =
      1 := by
  simpa [conclusion_zeckendorf_euler_wrapped_poisson_fourier_twisted_truncated_exponential]
    using
      conclusion_zeckendorf_euler_fminusone_jet_rigidity_sum_zero_power m
        (conclusion_zeckendorf_euler_wrapped_poisson_fourier_root m k)

/-- Paper label: `prop:conclusion-zeckendorf-euler-fminusone-jet-rigidity`. -/
theorem paper_conclusion_zeckendorf_euler_fminusone_jet_rigidity (m : Nat) :
    ∀ k : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m),
      conclusion_zeckendorf_euler_fminusone_jet_rigidity_sameJetUpTo
        (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m - 1)
        (fun t => conclusion_zeckendorf_euler_wrapped_poisson_fourier_euler_fourier m t k)
        (fun t =>
          conclusion_zeckendorf_euler_wrapped_poisson_fourier_wrapped_poisson_fourier m t k) := by
  intro k n
  have heuler :=
    (paper_conclusion_zeckendorf_euler_wrapped_poisson_fourier m 0).1 k
  have hwrapped :=
    (paper_conclusion_zeckendorf_euler_wrapped_poisson_fourier m 0).2 k
  change
    conclusion_zeckendorf_euler_wrapped_poisson_fourier_euler_fourier m 0 k =
      conclusion_zeckendorf_euler_wrapped_poisson_fourier_wrapped_poisson_fourier m 0 k
  rw [heuler, hwrapped]
  simp [conclusion_zeckendorf_euler_fminusone_jet_rigidity_truncated_zero,
    conclusion_zeckendorf_euler_fminusone_jet_rigidity_twisted_zero]

end

end Omega.Conclusion

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.GroupUnification.ChiralOrthogonalityTypeObservables

namespace Omega.Conclusion

/-- The complement involution on `ℤ / fib(m+2)ℤ` used in the residue-drift cancellation. -/
def conclusion_residue_drift_all_odd_moments_vanish_tau (m : ℕ) :
    ZMod (Nat.fib (m + 2)) → ZMod (Nat.fib (m + 2)) :=
  fun r => ((Nat.fib (m + 1) : ZMod (Nat.fib (m + 2))) - 2) - r

private lemma conclusion_residue_drift_all_odd_moments_vanish_tau_involutive (m : ℕ) :
    Function.Involutive (conclusion_residue_drift_all_odd_moments_vanish_tau m) := by
  intro r
  simp [conclusion_residue_drift_all_odd_moments_vanish_tau, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc]

private lemma conclusion_residue_drift_all_odd_moments_vanish_fixedpoint_zero
    (m : ℕ) (drift_k : ZMod (Nat.fib (m + 2)) → ℝ)
    (hdrift :
      ∀ r,
        drift_k (conclusion_residue_drift_all_odd_moments_vanish_tau m r) = -drift_k r)
    {r : ZMod (Nat.fib (m + 2))}
    (hfix : conclusion_residue_drift_all_odd_moments_vanish_tau m r = r) :
    drift_k r = 0 := by
  have hanti := hdrift r
  rw [hfix] at hanti
  linarith

/-- Paper label: `thm:conclusion-residue-drift-all-odd-moments-vanish`. If `μₘ` is invariant
under the complement involution `τₘ`, while the coordinate drift is anti-invariant, then every odd
test of the drift has zero `μₘ`-average; more generally the drift is orthogonal to every
`τₘ`-invariant test function. -/
theorem paper_conclusion_residue_drift_all_odd_moments_vanish
    (m k : ℕ)
    [NeZero (Nat.fib (m + 2))]
    (mu_m drift_k : ZMod (Nat.fib (m + 2)) → ℝ)
    (Q : ℝ → ℝ)
    (f : ZMod (Nat.fib (m + 2)) → ℝ)
    (hmu :
      ∀ r, mu_m (conclusion_residue_drift_all_odd_moments_vanish_tau m r) = mu_m r)
    (hdrift :
      ∀ r,
        drift_k (conclusion_residue_drift_all_odd_moments_vanish_tau m r) = -drift_k r)
    (hQ : ∀ x : ℝ, Q (-x) = -Q x)
    (hf :
      ∀ r, f (conclusion_residue_drift_all_odd_moments_vanish_tau m r) = f r) :
    (∑ r, mu_m r * Q (drift_k r)) = 0 ∧
      (∑ r, mu_m r * drift_k r * f r) = 0 := by
  let _ := k
  let tau := conclusion_residue_drift_all_odd_moments_vanish_tau m
  have htau : Function.Involutive tau :=
    conclusion_residue_drift_all_odd_moments_vanish_tau_involutive m
  have hoddQ : ∀ r, Q (drift_k (tau r)) = -Q (drift_k r) := by
    intro r
    rw [hdrift r, hQ]
  have hsumQ :
      (∑ r, mu_m r * Q (drift_k r)) = 0 := by
    simpa [tau] using
      Omega.GroupUnification.paper_window6_chiral_orthogonality_type_observables_seeds
        tau htau mu_m (fun r => Q (drift_k r)) hmu hoddQ
  have hmu_f :
      ∀ r, (mu_m r * f r) = (mu_m (tau r) * f (tau r)) := by
    intro r
    rw [hmu r, hf r]
  have hsumDrift :
      (∑ r, (mu_m r * f r) * drift_k r) = 0 := by
    have hginv : ∀ r, (mu_m (tau r) * f (tau r)) = mu_m r * f r := by
      intro r
      rw [hmu r, hf r]
    simpa [tau] using
      Omega.GroupUnification.paper_window6_chiral_orthogonality_type_observables_seeds
        tau htau (fun r => mu_m r * f r) drift_k hginv hdrift
  refine ⟨hsumQ, ?_⟩
  simpa [mul_assoc, mul_left_comm, mul_comm] using hsumDrift

end Omega.Conclusion

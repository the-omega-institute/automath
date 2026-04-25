import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittThetaDerivativeFilter

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- Finite Taylor jet used to model the `u = e^θ` flatness computation at the `p^k` stage: a
constant term, the stage-`k` linear coefficient, and finitely many higher terms. -/
def witt_padic_flatness_ball_taylor_jet (constant : ℤ) (linearCoeff : ℕ → ℤ)
    (higherCoeff : ℕ → ℕ → ℤ) (k N : ℕ) (θ : ℤ) : ℤ :=
  constant + linearCoeff (k - 1) * θ +
    Finset.sum (Finset.Icc 2 N) (fun r => higherCoeff r k * θ ^ r)

/-- Paper label: `cor:witt-padic-flatness-ball`. The existing derivative-divisibility filter gives
the `p^(k-1)` factor on the linear coefficient, while the higher Taylor coefficients are supplied
already `p^k`-divisible; together with `θ ∈ pℤ`, the truncated Taylor jet is flat modulo `p^k`. -/
theorem paper_witt_padic_flatness_ball
    (p k N : ℕ) (hp : Nat.Prime p) (hk : 1 ≤ k) (constant : ℤ)
    (linearCoeff : ℕ → ℤ) (higherCoeff : ℕ → ℕ → ℤ) (θ : ℤ)
    (hθ : ((p : ℤ) ∣ θ))
    (hscale : wittThetaDerivativeScaling p 1 linearCoeff)
    (hhigher : ∀ r, 2 ≤ r → ((p ^ k : ℤ) ∣ higherCoeff r k)) :
    ((p ^ k : ℤ) ∣
      witt_padic_flatness_ball_taylor_jet constant linearCoeff higherCoeff k N θ - constant) := by
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hfilter :=
    paper_witt_theta_derivative_filter p 1 hp (by norm_num) linearCoeff hscale
  have hlinearCoeff : ((p ^ k' : ℤ) ∣ linearCoeff k') := hfilter.2 k'
  have hlinearTerm : ((p ^ (k' + 1) : ℤ) ∣ linearCoeff k' * θ) := by
    simpa [pow_succ', mul_assoc, mul_comm, mul_left_comm] using mul_dvd_mul hlinearCoeff hθ
  have hhigherTerm :
      ∀ r ∈ Finset.Icc 2 N, ((p ^ (k' + 1) : ℤ) ∣ higherCoeff r (k' + 1) * θ ^ r) := by
    intro r hr
    exact dvd_mul_of_dvd_left (hhigher r (Finset.mem_Icc.mp hr).1) (θ ^ r)
  have hsum :
      ((p ^ (k' + 1) : ℤ) ∣
        Finset.sum (Finset.Icc 2 N) (fun r => higherCoeff r (k' + 1) * θ ^ r)) :=
    Finset.dvd_sum hhigherTerm
  have hsplit :
      witt_padic_flatness_ball_taylor_jet constant linearCoeff higherCoeff (k' + 1) N θ -
          constant =
        linearCoeff k' * θ +
          Finset.sum (Finset.Icc 2 N) (fun r => higherCoeff r (k' + 1) * θ ^ r) := by
    simp [witt_padic_flatness_ball_taylor_jet, mul_comm]
    ring_nf
  simpa [hsplit] using Int.dvd_add hlinearTerm hsum

end Omega.SyncKernelWeighted

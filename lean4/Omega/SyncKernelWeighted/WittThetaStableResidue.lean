import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittThetaDerivativeFilter

namespace Omega.SyncKernelWeighted

/-- The normalized residue class attached to the filtered theta-derivative stage `A k`. -/
def witt_theta_stable_residue_normalized (p : ℕ) (A : ℕ → ℤ) (k : ℕ) : ZMod p :=
  ((A k / (p ^ k : ℤ)) : ZMod p)

lemma witt_theta_stable_residue_normalized_eq
    (p : ℕ) (hp0 : p ≠ 0) (A : ℕ → ℤ) (k : ℕ) (q : ℤ) (hq : A k = (p ^ k : ℤ) * q) :
    witt_theta_stable_residue_normalized p A k = (q : ZMod p) := by
  unfold witt_theta_stable_residue_normalized
  rw [hq]
  have hk_ne : (p ^ k : ℤ) ≠ 0 := by
    exact_mod_cast pow_ne_zero k hp0
  rw [Int.mul_ediv_cancel_left _ hk_ne]

/-- Paper label: `cor:witt-theta-stable-residue`. Reindexing the theta-derivative tower turns the
paper's levels `k > r` into the filtered stages `k ≥ 1`. The derivative-filter theorem supplies
the divisibility `p^k ∣ A k`, and the Frobenius scaling congruence then shows that the normalized
residue class `p^{-k} A k (mod p)` is independent of the chosen stage once `k ≥ 1`. -/
theorem paper_witt_theta_stable_residue (p r : ℕ) (_hp : Nat.Prime p) (hr : 1 ≤ r)
    (A : ℕ → ℤ) (hscale : wittThetaDerivativeScaling p r A) :
    ∀ k, 1 ≤ k →
      witt_theta_stable_residue_normalized p A k =
        witt_theta_stable_residue_normalized p A 1 := by
  have hfiltered : wittThetaDerivativeFiltered p A :=
    (paper_witt_theta_derivative_filter p r _hp hr A hscale).2
  have hp0 : p ≠ 0 := _hp.ne_zero
  by_cases hr1 : r = 1
  · subst hr1
    have hstep :
        ∀ k,
          witt_theta_stable_residue_normalized p A (k + 1) =
            witt_theta_stable_residue_normalized p A k := by
      intro k
      rcases hfiltered k with ⟨qk, hqk⟩
      rcases hscale k with ⟨t, ht⟩
      have ht' : A (k + 1) - (p : ℤ) * A k = (p ^ (k + 2) : ℤ) * t := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
      have hnext :
          A (k + 1) = (p ^ (k + 1) : ℤ) * (qk + (p : ℤ) * t) := by
        calc
          A (k + 1) = (A (k + 1) - (p : ℤ) * A k) + (p : ℤ) * A k := by ring
          _ = (p ^ (k + 2) : ℤ) * t + (p : ℤ) * ((p ^ k : ℤ) * qk) := by rw [ht', hqk]
          _ = (p ^ (k + 1) : ℤ) * (qk + (p : ℤ) * t) := by
            rw [show k + 2 = (k + 1) + 1 by omega, pow_add, pow_one]
            ring
      calc
        witt_theta_stable_residue_normalized p A (k + 1)
            = ((qk + (p : ℤ) * t : ℤ) : ZMod p) := by
                rw [witt_theta_stable_residue_normalized_eq p hp0 A (k + 1)
                  (qk + (p : ℤ) * t) hnext]
        _ = (qk : ZMod p) := by simp
        _ = witt_theta_stable_residue_normalized p A k := by
              rw [witt_theta_stable_residue_normalized_eq p hp0 A k qk hqk]
    have hstable :
        ∀ n,
          witt_theta_stable_residue_normalized p A (n + 1) =
            witt_theta_stable_residue_normalized p A 1 := by
      intro n
      induction n with
      | zero =>
          rfl
      | succ n ih =>
          calc
            witt_theta_stable_residue_normalized p A (n + 2)
                = witt_theta_stable_residue_normalized p A (n + 1) := by
                    simpa [Nat.add_assoc] using hstep (n + 1)
            _ = witt_theta_stable_residue_normalized p A 1 := ih
    intro k hk
    rcases Nat.exists_eq_add_of_le hk with ⟨n, rfl⟩
    simpa [Nat.add_comm] using hstable n
  · have hr2 : 2 ≤ r := by omega
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr2
    have hzero :
        ∀ k, witt_theta_stable_residue_normalized p A (k + 1) = 0 := by
      intro k
      rcases hfiltered k with ⟨qk, hqk⟩
      rcases hscale k with ⟨t, ht⟩
      have ht' : A (k + 1) - (p ^ (s + 2) : ℤ) * A k = (p ^ (k + s + 3) : ℤ) * t := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
      have hnext :
          A (k + 1) =
            (p ^ (k + 1) : ℤ) *
              (((p ^ (s + 1) : ℤ) * qk) + ((p ^ (s + 2) : ℤ) * t)) := by
        calc
          A (k + 1)
              = (A (k + 1) - (p ^ (s + 2) : ℤ) * A k) + (p ^ (s + 2) : ℤ) * A k := by
                  ring
          _ = (p ^ (k + s + 3) : ℤ) * t + (p ^ (s + 2) : ℤ) * ((p ^ k : ℤ) * qk) := by
                rw [ht', hqk]
          _ = (p ^ (k + 1) : ℤ) * (((p ^ (s + 1) : ℤ) * qk) + ((p ^ (s + 2) : ℤ) * t)) := by
                rw [show k + s + 3 = (k + 1) + (s + 2) by omega, pow_add,
                  show s + 2 = (s + 1) + 1 by omega, pow_add, pow_one]
                ring
      calc
        witt_theta_stable_residue_normalized p A (k + 1)
            = ((((p ^ (s + 1) : ℤ) * qk) + ((p ^ (s + 2) : ℤ) * t) : ℤ) : ZMod p) := by
                rw [witt_theta_stable_residue_normalized_eq p hp0 A (k + 1)
                  (((p ^ (s + 1) : ℤ) * qk) + ((p ^ (s + 2) : ℤ) * t)) hnext]
        _ = 0 := by
              simp [pow_succ, mul_assoc]
    intro k hk
    rcases Nat.exists_eq_add_of_le hk with ⟨n, rfl⟩
    calc
      witt_theta_stable_residue_normalized p A (1 + n) = 0 := by
        simpa [Nat.add_comm] using hzero n
      _ = witt_theta_stable_residue_normalized p A 1 := by
        symm
        simpa using hzero 0

end Omega.SyncKernelWeighted

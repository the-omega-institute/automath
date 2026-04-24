import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Reindexed `r`-th theta-derivative moments along the Witt tower: `A k` stands for the
stage `A_{p^(r+k)}^(r)`. -/
def wittThetaDerivativeScaling (p r : ℕ) (A : ℕ → ℤ) : Prop :=
  ∀ k, ((p ^ (r + k + 1) : ℤ) ∣ A (k + 1) - (p ^ r : ℤ) * A k)

/-- Reindexed version of the `p^(k-r)` divisibility statement from the paper. -/
def wittThetaDerivativeFiltered (p : ℕ) (A : ℕ → ℤ) : Prop :=
  ∀ k, ((p ^ k : ℤ) ∣ A k)

lemma int_natPow_dvd_int_natPow (p : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ((p ^ a : ℤ) ∣ (p ^ b : ℤ)) := by
  rcases pow_dvd_pow p hab with ⟨t, ht⟩
  refine ⟨(t : ℤ), ?_⟩
  exact_mod_cast ht

/-- Paper label: `prop:witt-theta-derivative-filter`.
The Dwork congruence for the reindexed theta-derivative moments gives the stagewise scaling
congruence, and when `r ≥ 1` it forces one additional factor of `p` at every step. -/
theorem paper_witt_theta_derivative_filter (p r : ℕ) (_hp : Nat.Prime p) (hr : 1 ≤ r)
    (A : ℕ → ℤ) :
    wittThetaDerivativeScaling p r A → wittThetaDerivativeScaling p r A ∧
      wittThetaDerivativeFiltered p A := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hr)
  intro hdwork
  refine ⟨hdwork, ?_⟩
  intro k
  induction k with
  | zero =>
      exact ⟨A 0, by simp⟩
  | succ k ih =>
      have hdefectStrong :
          ((p ^ (Nat.succ s + k + 1) : ℤ) ∣
            A (k + 1) - (p ^ Nat.succ s : ℤ) * A k) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdwork k
      have hdefect :
          ((p ^ (k + 1) : ℤ) ∣ A (k + 1) - (p ^ Nat.succ s : ℤ) * A k) := by
        exact dvd_trans (int_natPow_dvd_int_natPow p (by omega)) hdefectStrong
      have hpFactor : ((p : ℤ) ∣ (p ^ Nat.succ s : ℤ)) := by
        refine ⟨(p ^ s : ℤ), ?_⟩
        simp [pow_succ']
      have hscaled : ((p ^ (k + 1) : ℤ) ∣ (p ^ Nat.succ s : ℤ) * A k) := by
        simpa [pow_succ', mul_assoc, mul_comm, mul_left_comm] using mul_dvd_mul hpFactor ih
      have hsplit :
          A (k + 1) =
            (A (k + 1) - (p ^ Nat.succ s : ℤ) * A k) + (p ^ Nat.succ s : ℤ) * A k := by
        ring
      rw [hsplit]
      exact Int.dvd_add hdefect hscaled

end Omega.SyncKernelWeighted

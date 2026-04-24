import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Split a finite truncated power-series sum into its residue classes modulo `m`. -/
theorem abel_polyphase_reconstruction_sum_split {R : Type*} [CommSemiring R]
    (a : ℕ → R) (m N : ℕ) (r : R) :
    Finset.sum (Finset.range (m * N)) (fun n => a n * r ^ n) =
      Finset.sum (Finset.range m)
        (fun j => r ^ j * Finset.sum (Finset.range N) (fun q => a (m * q + j) * (r ^ m) ^ q)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      calc
        Finset.sum (Finset.range (m * N.succ)) (fun n => a n * r ^ n)
            = Finset.sum (Finset.range (m * N + m)) (fun n => a n * r ^ n) := by
                simp [Nat.mul_succ, Nat.add_comm]
        _ = Finset.sum (Finset.range (m * N)) (fun n => a n * r ^ n) +
              Finset.sum (Finset.range m) (fun j => a (m * N + j) * r ^ (m * N + j)) := by
                rw [Finset.sum_range_add]
        _ = Finset.sum (Finset.range m)
              (fun j => r ^ j * Finset.sum (Finset.range N) (fun q => a (m * q + j) * (r ^ m) ^ q)) +
              Finset.sum (Finset.range m) (fun j => a (m * N + j) * r ^ (m * N + j)) := by
                rw [ih]
        _ = Finset.sum (Finset.range m)
              (fun j => r ^ j * Finset.sum (Finset.range N) (fun q => a (m * q + j) * (r ^ m) ^ q)) +
              Finset.sum (Finset.range m) (fun j => r ^ j * (a (m * N + j) * (r ^ m) ^ N)) := by
                congr 1
                apply Finset.sum_congr rfl
                intro j hj
                rw [pow_add, pow_mul]
                simp [mul_left_comm, mul_comm]
        _ = Finset.sum (Finset.range m) (fun j =>
              (r ^ j * Finset.sum (Finset.range N) (fun q => a (m * q + j) * (r ^ m) ^ q)) +
                (r ^ j * (a (m * N + j) * (r ^ m) ^ N))) := by
                rw [← Finset.sum_add_distrib]
        _ = Finset.sum (Finset.range m) (fun j =>
              r ^ j * (Finset.sum (Finset.range N) (fun q => a (m * q + j) * (r ^ m) ^ q) +
                a (m * N + j) * (r ^ m) ^ N)) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [mul_add]
        _ = Finset.sum (Finset.range m)
              (fun j => r ^ j * Finset.sum (Finset.range N.succ) (fun q => a (m * q + j) * (r ^ m) ^ q)) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [Finset.sum_range_succ, mul_add]

/-- Paper label: `prop:abel-polyphase-reconstruction`. -/
theorem paper_abel_polyphase_reconstruction (a : ℕ → ℤ) (m N : ℕ) (r : ℤ) :
    Finset.sum (Finset.range (m * N)) (fun n => a n * r ^ n) =
      Finset.sum (Finset.range m)
        (fun j => r ^ j * Finset.sum (Finset.range N) (fun q => a (m * q + j) * (r ^ m) ^ q)) := by
  simpa using abel_polyphase_reconstruction_sum_split (R := ℤ) a m N r

end Omega.Zeta

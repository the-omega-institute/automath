import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Divisors

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Concrete finite/truncated data for the divisor-compressed `q`-axis Ramanujan package. -/
structure conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data where
  q : ℕ
  cutoff : ℕ
  coeff : ℕ → ℝ

/-- The positive conductor used on the compressed `q`-axis. -/
def conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_conductor
    (D : conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data) : ℕ :=
  D.q + 1

/-- The finite positive support replacing the infinite coefficient sum. -/
def conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_support
    (D : conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data) : Finset ℕ :=
  Finset.Icc 1 D.cutoff

/-- A divisor atom whose divisor sum is the usual indicator `q ∣ n` times `q`. -/
def conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom
    (q m n : ℕ) : ℝ :=
  if m = q ∧ q ∣ n then (q : ℝ) else 0

/-- The diagonal atom produced by the finite divisor-sum identity. -/
def conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_diagonal_atom
    (q n : ℕ) : ℝ :=
  if q ∣ n then (q : ℝ) else 0

/-- The divisor-expanded compressed signal. -/
def conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_expanded_signal
    (D : conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data) : ℝ :=
  let q := conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_conductor D
  Finset.sum q.divisors fun m =>
    Finset.sum (conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_support D) fun n =>
      D.coeff n / (n : ℝ) *
        conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom q m n

/-- The diagonalized finite `q`-axis signal. -/
def conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_diagonal_signal
    (D : conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data) : ℝ :=
  let q := conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_conductor D
  Finset.sum (conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_support D) fun n =>
    D.coeff n / (n : ℝ) *
      conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_diagonal_atom q n

lemma conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_divisor_atom_sum
    (q n : ℕ) (hq : 0 < q) :
    (Finset.sum q.divisors fun m =>
      conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom q m n) =
      conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_diagonal_atom q n := by
  have hq_ne : q ≠ 0 := Nat.ne_of_gt hq
  by_cases hdiv : q ∣ n
  · rw [conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_diagonal_atom]
    simp only [hdiv, ↓reduceIte]
    calc
      (Finset.sum q.divisors fun m =>
          conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom q m n)
          =
          conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom q q n := by
            refine Finset.sum_eq_single (s := q.divisors)
              (f := fun m =>
                conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom q m n)
              (a := q) ?_ ?_
            · intro m hm hmq
              simp [conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom,
                hmq, hdiv]
            · intro hnot
              exact False.elim (hnot (Nat.mem_divisors.mpr ⟨dvd_rfl, hq_ne⟩))
      _ = (q : ℝ) := by
        simp [conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom,
          hdiv]
  · simp [conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom,
      conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_diagonal_atom, hdiv]

namespace conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data

/-- The finite divisor-compressed `q`-axis identity. -/
def qaxis_identity
    (D : conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data) : Prop :=
  conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_expanded_signal D =
    conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_diagonal_signal D

end conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data

/-- Paper label:
`thm:conclusion-divisor-compressed-qaxis-ramanujan-diagonalization`. -/
theorem paper_conclusion_divisor_compressed_qaxis_ramanujan_diagonalization
    (D : conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data) :
    D.qaxis_identity := by
  classical
  let q := conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_conductor D
  have hq : 0 < q := by
    simp [q, conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_conductor]
  rw [conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_data.qaxis_identity,
    conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_expanded_signal,
    conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_diagonal_signal]
  change
    (Finset.sum q.divisors fun m =>
      Finset.sum (conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_support D) fun n =>
        D.coeff n / (n : ℝ) *
          conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_ramanujan_atom q m n) =
      Finset.sum (conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_support D) fun n =>
        D.coeff n / (n : ℝ) *
          conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_diagonal_atom q n
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [← Finset.mul_sum,
    conclusion_divisor_compressed_qaxis_ramanujan_diagonalization_divisor_atom_sum q n hq]

end

end Omega.Conclusion

import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset Matrix
open scoped BigOperators

/-- Concrete regular-polygon data supplied by the equality-rigidity theorem. -/
structure conclusion_toeplitz_flat_horizon_from_one_inner_equality_data where
  N : ℕ
  eta : ℂ
  root : ℂ
  N_pos : 1 ≤ N
  eta_ne_zero : eta ≠ 0
  regular_polygon_rigidity : IsPrimitiveRoot root (N + 1)

/-- The finite root-of-unity coefficient attached to the regular `(N+1)`-polygon. -/
noncomputable def conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff
    (D : conclusion_toeplitz_flat_horizon_from_one_inner_equality_data) (j : ℕ) : ℂ :=
  D.eta / (D.N + 1 : ℂ) * ∑ k ∈ range (D.N + 1), (D.root ^ j) ^ k

/-- Toeplitz block built from the finite root-of-unity coefficients. -/
noncomputable def conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz
    (D : conclusion_toeplitz_flat_horizon_from_one_inner_equality_data) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j =>
    if i = j then D.eta
    else
      conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff D
        (max i.val j.val - min i.val j.val)

/-- Concrete statement of the finite flatness horizon. -/
def conclusion_toeplitz_flat_horizon_from_one_inner_equality_statement
    (D : conclusion_toeplitz_flat_horizon_from_one_inner_equality_data) : Prop :=
  (∀ j, 1 ≤ j → j ≤ D.N →
      conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff D j = 0) ∧
    conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff D (D.N + 1) = D.eta ∧
    conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff D (D.N + 1) ≠ 0 ∧
    (∀ m, m ≤ D.N →
      conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz D m =
        D.eta • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) ∧
    conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz D (D.N + 1) ≠
      D.eta • (1 : Matrix (Fin (D.N + 2)) (Fin (D.N + 2)) ℂ)

lemma conclusion_toeplitz_flat_horizon_from_one_inner_equality_root_sum_zero
    (D : conclusion_toeplitz_flat_horizon_from_one_inner_equality_data) {j : ℕ}
    (hj0 : 1 ≤ j) (hjN : j ≤ D.N) :
    ∑ k ∈ range (D.N + 1), (D.root ^ j) ^ k = 0 := by
  have hj_ne_zero : j ≠ 0 := Nat.ne_of_gt hj0
  have hj_lt : j < D.N + 1 := Nat.lt_succ_of_le hjN
  have hne : D.root ^ j ≠ 1 :=
    D.regular_polygon_rigidity.pow_ne_one_of_pos_of_lt hj_ne_zero hj_lt
  have hpow : (D.root ^ j) ^ (D.N + 1) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, D.regular_polygon_rigidity.pow_eq_one, one_pow]
  have hmul := geom_sum_mul_neg (D.root ^ j) (D.N + 1)
  rw [hpow, sub_self] at hmul
  rcases mul_eq_zero.mp hmul with hsum | hsub
  · exact hsum
  · exact False.elim (sub_ne_zero.mpr hne.symm hsub)

lemma conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff_zero
    (D : conclusion_toeplitz_flat_horizon_from_one_inner_equality_data) {j : ℕ}
    (hj0 : 1 ≤ j) (hjN : j ≤ D.N) :
    conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff D j = 0 := by
  simp [conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff,
    conclusion_toeplitz_flat_horizon_from_one_inner_equality_root_sum_zero D hj0 hjN]

lemma conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff_next
    (D : conclusion_toeplitz_flat_horizon_from_one_inner_equality_data) :
    conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff D (D.N + 1) = D.eta := by
  have hn : (D.N + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero D.N
  simp [conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff,
    D.regular_polygon_rigidity.pow_eq_one, hn]

lemma conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz_flat
    (D : conclusion_toeplitz_flat_horizon_from_one_inner_equality_data) {m : ℕ}
    (hmN : m ≤ D.N) :
    conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz D m =
      D.eta • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  ext i j
  by_cases hij : i = j
  · simp [conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz, hij]
  · by_cases hij_le : i.val ≤ j.val
    · have hlt : i.val < j.val := by
        exact lt_of_le_of_ne hij_le (by simpa [Fin.ext_iff] using hij)
      have hpos : 1 ≤ j.val - i.val := by omega
      have hleN : j.val - i.val ≤ D.N := by
        have hjm : j.val ≤ m := Nat.le_of_lt_succ j.isLt
        omega
      simp [conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz, hij,
        Nat.max_eq_right hij_le, Nat.min_eq_left hij_le,
        conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff_zero D hpos hleN]
    · have hji_le : j.val ≤ i.val := le_of_not_ge hij_le
      have hlt : j.val < i.val := by
        exact lt_of_le_of_ne hji_le (by
          intro hvals
          exact hij (Fin.ext hvals.symm))
      have hpos : 1 ≤ i.val - j.val := by omega
      have hleN : i.val - j.val ≤ D.N := by
        have him : i.val ≤ m := Nat.le_of_lt_succ i.isLt
        omega
      simp [conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz, hij,
        Nat.max_eq_left hji_le, Nat.min_eq_right hji_le,
        conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff_zero D hpos hleN]

/-- Paper label: `thm:conclusion-toeplitz-flat-horizon-from-one-inner-equality`. -/
theorem paper_conclusion_toeplitz_flat_horizon_from_one_inner_equality
    (D : conclusion_toeplitz_flat_horizon_from_one_inner_equality_data) :
    conclusion_toeplitz_flat_horizon_from_one_inner_equality_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj0 hjN
    exact conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff_zero D hj0 hjN
  · exact conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff_next D
  · rw [conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff_next]
    exact D.eta_ne_zero
  · intro m hmN
    exact conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz_flat D hmN
  · intro hflat
    let i : Fin (D.N + 2) := ⟨0, by omega⟩
    let j : Fin (D.N + 2) := ⟨D.N + 1, by omega⟩
    have hentry := congr_fun (congr_fun hflat i) j
    have hcoeff :=
      conclusion_toeplitz_flat_horizon_from_one_inner_equality_coeff_next D
    have hij : i ≠ j := by
      intro h
      exact Nat.succ_ne_zero D.N (by simpa [i, j] using congrArg Fin.val h)
    simp [conclusion_toeplitz_flat_horizon_from_one_inner_equality_toeplitz, i, j,
      hcoeff] at hentry
    exact D.eta_ne_zero hentry

end Omega.Conclusion

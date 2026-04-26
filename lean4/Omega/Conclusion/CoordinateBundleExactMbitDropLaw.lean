import Mathlib.Tactic
import Omega.Conclusion.CoordinateBundleLogmodularityVisibleRank

namespace Omega.Conclusion

/-- Hidden volume of an internal coordinate-bundle screen. -/
def conclusion_coordinate_bundle_exact_mbit_drop_law_delta (m n : Nat)
    (J : Finset (Fin n)) : Nat :=
  2 ^ (m * (n - J.card))

/-- Visible rank obtained by subtracting the hidden volume from the full top-cell count. -/
def conclusion_coordinate_bundle_exact_mbit_drop_law_visibleRank (m n : Nat)
    (J : Finset (Fin n)) : Nat :=
  2 ^ (m * n) - conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n J

/-- Combined exact `m`-bit drop and visible-rank increment for adjoining one new coordinate. -/
def conclusion_coordinate_bundle_exact_mbit_drop_law_statement (m n : Nat)
    (J : Finset (Fin n)) (j : Fin n) : Prop :=
  conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n J =
      2 ^ m * conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n (insert j J) ∧
    conclusion_coordinate_bundle_exact_mbit_drop_law_visibleRank m n (insert j J) =
      conclusion_coordinate_bundle_exact_mbit_drop_law_visibleRank m n J +
        (2 ^ m - 1) *
          conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n (insert j J)

/-- Paper label: `thm:conclusion-coordinate-bundle-exact-mbit-drop-law`. -/
theorem paper_conclusion_coordinate_bundle_exact_mbit_drop_law
    (m n : Nat) (J : Finset (Fin n)) (j : Fin n) (hj : j ∉ J) :
    conclusion_coordinate_bundle_exact_mbit_drop_law_statement m n J j := by
  have hcard_insert : (insert j J).card = J.card + 1 := by
    exact Finset.card_insert_of_notMem hj
  have hJ_lt : J.card < n := by
    have hle : (insert j J).card ≤ n := by simpa using (insert j J).card_le_univ
    omega
  have hhidden :
      n - J.card = n - (insert j J).card + 1 := by
    omega
  have hdelta :
      conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n J =
        2 ^ m * conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n (insert j J) := by
    calc
      conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n J =
          2 ^ (m * (n - J.card)) := rfl
      _ = 2 ^ (m * (n - (insert j J).card + 1)) := by rw [hhidden]
      _ = 2 ^ (m * (n - (insert j J).card) + m) := by rw [Nat.mul_add, Nat.mul_one]
      _ = 2 ^ (m * (n - (insert j J).card)) * 2 ^ m := by rw [pow_add]
      _ = 2 ^ m * 2 ^ (m * (n - (insert j J).card)) := by rw [Nat.mul_comm]
      _ =
          2 ^ m *
            conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n (insert j J) := rfl
  refine ⟨hdelta, ?_⟩
  unfold conclusion_coordinate_bundle_exact_mbit_drop_law_visibleRank
  let total := 2 ^ (m * n)
  let small := conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n (insert j J)
  have hsmall_le_total : small ≤ total := by
    have hexp : m * (n - (insert j J).card) ≤ m * n := by
      exact Nat.mul_le_mul_left m (Nat.sub_le n (insert j J).card)
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
  have hbig_le_total :
      conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n J ≤ total := by
    have hexp : m * (n - J.card) ≤ m * n := by
      exact Nat.mul_le_mul_left m (Nat.sub_le n J.card)
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
  have hpow_pos : 0 < 2 ^ m := pow_pos (by norm_num : (0 : Nat) < 2) m
  have hbig : conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n J = 2 ^ m * small := by
    simpa [small] using hdelta
  have hbig_split :
      conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n J =
        small + (2 ^ m - 1) * small := by
    rw [hbig]
    have hpow_pred : 1 + (2 ^ m - 1) = 2 ^ m := by omega
    calc
      2 ^ m * small = (1 + (2 ^ m - 1)) * small := by rw [hpow_pred]
      _ = small + (2 ^ m - 1) * small := by rw [Nat.add_mul, one_mul]
  have hbig_split' :
      conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n J =
        conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n (insert j J) +
          (2 ^ m - 1) *
            conclusion_coordinate_bundle_exact_mbit_drop_law_delta m n (insert j J) := by
    simpa [small] using hbig_split
  omega

end Omega.Conclusion

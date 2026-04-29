import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the normalized local Smith numerator Newton staircase.

The profile `f` is the local Smith counting function, `Emax` is the stabilized largest
local exponent, and `Esum` is the terminal total exponent. -/
structure conclusion_smith_normalized_local_numerator_newton_staircase_data where
  p : ℕ
  Emax : ℕ
  Esum : ℕ
  f : ℕ → ℕ
  p_prime : p.Prime
  f_zero : f 0 = 0
  f_strict_on_staircase : ∀ k, 1 ≤ k → k ≤ Emax → f (k - 1) < f k
  f_stabilized_value : f Emax = Esum

/-- The one-step Smith exponent jump. -/
def conclusion_smith_normalized_local_numerator_newton_staircase_delta
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) (k : ℕ) : ℕ :=
  D.f k - D.f (k - 1)

/-- Coefficients of the normalized local numerator.  The constant coefficient is `1`; positive
coefficients are written in the Smith/Newton factored form. -/
def conclusion_smith_normalized_local_numerator_newton_staircase_coeff
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) (k : ℕ) : ℕ :=
  if k = 0 then
    1
  else
    D.p ^ D.f (k - 1) *
      (D.p ^ conclusion_smith_normalized_local_numerator_newton_staircase_delta D k - 1)

/-- The partial coefficient sum `1 + q_1 + ... + q_k`. -/
def conclusion_smith_normalized_local_numerator_newton_staircase_cumulative
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) (k : ℕ) : ℕ :=
  1 +
    (Finset.range k).sum
      (fun i => conclusion_smith_normalized_local_numerator_newton_staircase_coeff D (i + 1))

/-- The valuation read from a positive Newton coefficient. -/
def conclusion_smith_normalized_local_numerator_newton_staircase_coeffValuation
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) (k : ℕ) : ℕ :=
  D.f (k - 1)

/-- The Newton step recovered from adjacent cumulative powers. -/
def conclusion_smith_normalized_local_numerator_newton_staircase_recoveredDelta
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) (k : ℕ) : ℕ :=
  D.f k - D.f (k - 1)

/-- The numerator value at `X = 1`, encoded as the terminal cumulative coefficient sum. -/
def conclusion_smith_normalized_local_numerator_newton_staircase_valueAtOne
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) : ℕ :=
  conclusion_smith_normalized_local_numerator_newton_staircase_cumulative D D.Emax

/-- The finite degree read from the stabilized staircase endpoint. -/
def conclusion_smith_normalized_local_numerator_newton_staircase_degree
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) : ℕ :=
  D.Emax

/-- Concrete statement of the normalized local numerator Newton staircase. -/
def conclusion_smith_normalized_local_numerator_newton_staircase_statement
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) : Prop :=
  (∀ k, 1 ≤ k → k ≤ D.Emax →
    conclusion_smith_normalized_local_numerator_newton_staircase_coeff D k =
      D.p ^ D.f (k - 1) *
        (D.p ^ conclusion_smith_normalized_local_numerator_newton_staircase_delta D k - 1)) ∧
  (∀ k, k ≤ D.Emax →
    conclusion_smith_normalized_local_numerator_newton_staircase_cumulative D k = D.p ^ D.f k) ∧
  (∀ k, 1 ≤ k → k ≤ D.Emax →
    conclusion_smith_normalized_local_numerator_newton_staircase_coeffValuation D k =
      D.f (k - 1)) ∧
  (∀ k, 1 ≤ k → k ≤ D.Emax →
    conclusion_smith_normalized_local_numerator_newton_staircase_recoveredDelta D k =
      conclusion_smith_normalized_local_numerator_newton_staircase_delta D k) ∧
  conclusion_smith_normalized_local_numerator_newton_staircase_valueAtOne D = D.p ^ D.Esum ∧
  conclusion_smith_normalized_local_numerator_newton_staircase_degree D = D.Emax

lemma conclusion_smith_normalized_local_numerator_newton_staircase_cumulative_holds
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) :
    ∀ k, k ≤ D.Emax →
      conclusion_smith_normalized_local_numerator_newton_staircase_cumulative D k =
        D.p ^ D.f k := by
  intro k hk
  induction k with
  | zero =>
      simp [conclusion_smith_normalized_local_numerator_newton_staircase_cumulative, D.f_zero]
  | succ k ih =>
      have hkE : k ≤ D.Emax := Nat.le_trans (Nat.le_succ k) hk
      have hstrict :
          D.f ((k + 1) - 1) < D.f (k + 1) :=
        D.f_strict_on_staircase (k + 1) (Nat.succ_pos k) hk
      have hpred : (k + 1) - 1 = k := Nat.succ_sub_one k
      have hle : D.f k ≤ D.f (k + 1) := by
        simpa [hpred] using hstrict.le
      have hdelta :
          D.f k +
              conclusion_smith_normalized_local_numerator_newton_staircase_delta D (k + 1) =
            D.f (k + 1) := by
        simp [conclusion_smith_normalized_local_numerator_newton_staircase_delta, hpred,
          Nat.add_sub_of_le hle]
      have hpow :
          D.p ^ D.f k *
              D.p ^ conclusion_smith_normalized_local_numerator_newton_staircase_delta D (k + 1) =
            D.p ^ D.f (k + 1) := by
        rw [← pow_add, hdelta]
      have hbase :
          1 ≤
            D.p ^
              conclusion_smith_normalized_local_numerator_newton_staircase_delta D (k + 1) :=
        Nat.one_le_pow (conclusion_smith_normalized_local_numerator_newton_staircase_delta D
          (k + 1)) D.p (Nat.succ_le_of_lt D.p_prime.pos)
      calc
        conclusion_smith_normalized_local_numerator_newton_staircase_cumulative D (k + 1)
            =
          conclusion_smith_normalized_local_numerator_newton_staircase_cumulative D k +
            conclusion_smith_normalized_local_numerator_newton_staircase_coeff D (k + 1) := by
              simp [conclusion_smith_normalized_local_numerator_newton_staircase_cumulative,
                Finset.sum_range_succ, Nat.add_assoc]
        _ =
          D.p ^ D.f k +
            D.p ^ D.f k *
              (D.p ^
                  conclusion_smith_normalized_local_numerator_newton_staircase_delta D (k + 1) -
                1) := by
              rw [ih hkE]
              simp [conclusion_smith_normalized_local_numerator_newton_staircase_coeff]
        _ =
          D.p ^ D.f k *
              D.p ^
                conclusion_smith_normalized_local_numerator_newton_staircase_delta D (k + 1) := by
              calc
                D.p ^ D.f k +
                    D.p ^ D.f k *
                      (D.p ^
                          conclusion_smith_normalized_local_numerator_newton_staircase_delta D
                            (k + 1) -
                        1)
                    =
                  D.p ^ D.f k * 1 +
                    D.p ^ D.f k *
                      (D.p ^
                          conclusion_smith_normalized_local_numerator_newton_staircase_delta D
                            (k + 1) -
                        1) := by simp
                _ =
                  D.p ^ D.f k *
                    (1 +
                      (D.p ^
                          conclusion_smith_normalized_local_numerator_newton_staircase_delta D
                            (k + 1) -
                        1)) := by
                  rw [← mul_add]
                _ =
                  D.p ^ D.f k *
                    D.p ^
                      conclusion_smith_normalized_local_numerator_newton_staircase_delta D
                        (k + 1) := by
                  rw [Nat.add_sub_of_le hbase]
        _ = D.p ^ D.f (k + 1) := hpow

/-- Paper label:
`thm:conclusion-smith-normalized-local-numerator-newton-staircase`. -/
theorem paper_conclusion_smith_normalized_local_numerator_newton_staircase
    (D : conclusion_smith_normalized_local_numerator_newton_staircase_data) :
    conclusion_smith_normalized_local_numerator_newton_staircase_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hkpos _hkE
    simp [conclusion_smith_normalized_local_numerator_newton_staircase_coeff,
      Nat.ne_of_gt hkpos]
  · exact conclusion_smith_normalized_local_numerator_newton_staircase_cumulative_holds D
  · intro k _hkpos _hkE
    rfl
  · intro k _hkpos _hkE
    rfl
  · unfold conclusion_smith_normalized_local_numerator_newton_staircase_valueAtOne
    rw [conclusion_smith_normalized_local_numerator_newton_staircase_cumulative_holds D D.Emax
      (le_rfl), D.f_stabilized_value]
  · rfl

end Omega.Conclusion

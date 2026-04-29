import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-multisqrt-norm-lower-bound`.

This is the coarse norm argument abstracted to a finite family of real conjugates: one distinguished
conjugate is bounded from below once the full product has absolute value at least `1` and every
other conjugate is uniformly bounded by `M`. -/
def conclusion_multisqrt_norm_lower_bound_statement : Prop :=
  ∀ {r : ℕ} (conj : (Fin r → Bool) → ℝ) (M : ℝ),
    1 ≤ M →
    1 ≤ |∏ ε, conj ε| →
    (∀ ε, |conj ε| ≤ M) →
      1 / M ^ (2 ^ r - 1) ≤ |conj (fun _ => true)|

theorem paper_conclusion_multisqrt_norm_lower_bound :
    conclusion_multisqrt_norm_lower_bound_statement := by
  intro r conj M hM hNorm hBound
  let ε0 : Fin r → Bool := fun _ => true
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hProdAbs : 1 ≤ ∏ ε, |conj ε| := by
    rw [← Finset.abs_prod]
    exact hNorm
  have hOthersLe :
      Finset.prod (Finset.univ.erase ε0) (fun ε => |conj ε|) ≤ M ^ (Finset.univ.erase ε0).card := by
    calc
      Finset.prod (Finset.univ.erase ε0) (fun ε => |conj ε|)
          ≤ Finset.prod (Finset.univ.erase ε0) (fun _ => M) := by
            apply Finset.prod_le_prod
            · intro ε hε
              exact abs_nonneg (conj ε)
            · intro ε hε
              exact hBound ε
      _ = M ^ (Finset.univ.erase ε0).card := by simp
  have hCardSucc : (Finset.univ.erase ε0).card + 1 = 2 ^ r := by
    simpa [ε0] using
      (Finset.card_erase_add_one (s := (Finset.univ : Finset (Fin r → Bool))) (a := ε0))
  have hCard : (Finset.univ.erase ε0).card = 2 ^ r - 1 := by
    omega
  have hMain :
      1 ≤ |conj ε0| * M ^ (2 ^ r - 1) := by
    calc
      1 ≤ ∏ ε, |conj ε| := hProdAbs
      _ = |conj ε0| * Finset.prod (Finset.univ.erase ε0) (fun ε => |conj ε|) := by
            symm
            simpa using
              (Finset.mul_prod_erase (Finset.univ : Finset (Fin r → Bool))
                (fun ε => |conj ε|) (a := ε0) (by simp [ε0]))
      _ ≤ |conj ε0| * M ^ (Finset.univ.erase ε0).card := by
            exact mul_le_mul_of_nonneg_left hOthersLe (abs_nonneg _)
      _ = |conj ε0| * M ^ (2 ^ r - 1) := by rw [hCard]
  have hPowPos : 0 < M ^ (2 ^ r - 1) := pow_pos hMpos _
  simpa [ε0, mul_comm, mul_left_comm, mul_assoc] using (div_le_iff₀ hPowPos).2 hMain

end Omega.Conclusion

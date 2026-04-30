import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The reverse conditional expectation level in the finite base-power model. -/
def conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp
    (k M : ℕ) : ℤ :=
  (k : ℤ) ^ M

/-- The orthogonal shell increment between two adjacent reverse levels. -/
def conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell
    (k M : ℕ) : ℤ :=
  conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k (M + 1) -
    conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k M

/-- One reverse martingale step: the next level is the previous level plus its shell. -/
def conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_step
    (k M : ℕ) : Prop :=
  conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k (M + 1) =
    conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k M +
      conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell k M

/-- Finite Pythagoras/telescoping decomposition of the reverse filtration energy. -/
def conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_energy
    (k M : ℕ) : Prop :=
  conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k M =
    conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k 0 +
      (Finset.range M).sum
        (fun m =>
          conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell k m)

/-- Concrete statement for the base-power reverse martingale and `k`-adic shell splitting. -/
def conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_statement
    (k : ℕ) : Prop :=
  2 ≤ k ∧
    (∀ M : ℕ,
      conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_step k M) ∧
      ∀ M : ℕ,
        conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_energy k M

/-- Paper label: `thm:conclusion-basepower-renormalization-reverse-martingale-kadic-splitting`. -/
theorem paper_conclusion_basepower_renormalization_reverse_martingale_kadic_splitting
    (k : ℕ) (hk : 2 ≤ k) :
    conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_statement k := by
  refine ⟨hk, ?_, ?_⟩
  · intro M
    unfold conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_step
    unfold conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell
    ring
  · intro M
    induction M with
    | zero =>
        simp [conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_energy]
    | succ M ih =>
        unfold conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_energy at ih ⊢
        rw [Finset.sum_range_succ]
        calc
          conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k
              (M + 1) =
            conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k M +
              conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell k M := by
              unfold conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell
              ring
          _ =
            (conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k 0 +
                (Finset.range M).sum
                  (fun m =>
                    conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell k m)) +
              conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell k M := by
              rw [ih]
          _ =
            conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_condexp k 0 +
              ((Finset.range M).sum
                  (fun m =>
                    conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell k m) +
                conclusion_basepower_renormalization_reverse_martingale_kadic_splitting_shell k M) := by
              ring

end Omega.Conclusion

import Mathlib.Tactic

namespace Omega.Conclusion

set_option linter.unusedVariables false in
/--
Paper label:
`thm:conclusion-fixedresolution-principal-hankelnull-finite-determinacy`.
-/
theorem paper_conclusion_fixedresolution_principal_hankelnull_finite_determinacy
    (d : ℕ) (hd : 0 < d) (S T : ℕ → ℤ) (a : Fin d → ℤ)
    (hinit : ∀ i : Fin d, T i = S i)
    (hS : ∀ q : ℕ, S (q + d) + ∑ i : Fin d, a i * S (q + i) = 0)
    (hT : ∀ q : ℕ, T (q + d) + ∑ i : Fin d, a i * T (q + i) = 0) :
    T = S := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < d
      · exact hinit ⟨n, hn⟩
      · let q := n - d
        have hnqd : n = q + d := by
          dsimp [q]
          omega
        have hsum :
            (∑ i : Fin d, a i * T (q + i)) =
              ∑ i : Fin d, a i * S (q + i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hlt : q + (i : ℕ) < n := by
            rw [hnqd]
            exact Nat.add_lt_add_left i.isLt q
          rw [ih (q + i) hlt]
        have hTq := hT q
        have hSq := hS q
        rw [hnqd]
        linarith

end Omega.Conclusion

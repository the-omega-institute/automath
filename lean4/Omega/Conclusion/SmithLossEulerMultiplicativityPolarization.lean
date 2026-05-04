import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-smith-loss-euler-multiplicativity-polarization`. -/
theorem paper_conclusion_smith_loss_euler_multiplicativity_polarization {m : ℕ}
    (d : Fin m → ℕ) :
    (∀ b c : ℕ, Nat.Coprime b c →
      (∏ i, Nat.gcd (d i) (b * c)) =
        (∏ i, Nat.gcd (d i) b) * (∏ i, Nat.gcd (d i) c)) ∧
      (∀ b : ℕ, (∀ i, Nat.Coprime b (d i)) → (∏ i, Nat.gcd (d i) b) = 1) ∧
      (∀ b : ℕ, 0 < b → (∀ i, b ∣ d i) → (∏ i, Nat.gcd (d i) b) = b ^ m) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro b c hbc
    calc
      (∏ i, Nat.gcd (d i) (b * c)) =
          ∏ i, Nat.gcd (d i) b * Nat.gcd (d i) c := by
        refine Finset.prod_congr rfl ?_
        intro i _
        simpa [Nat.gcd_comm] using hbc.gcd_mul (d i)
      _ = (∏ i, Nat.gcd (d i) b) * (∏ i, Nat.gcd (d i) c) := by
        rw [Finset.prod_mul_distrib]
  · intro b hb
    refine Finset.prod_eq_one ?_
    intro i _
    simpa [Nat.gcd_comm] using (hb i).gcd_eq_one
  · intro b hbpos hbdiv
    calc
      (∏ i, Nat.gcd (d i) b) = ∏ _i : Fin m, b := by
        refine Finset.prod_congr rfl ?_
        intro i _
        exact Nat.gcd_eq_right (hbdiv i)
      _ = b ^ m := by
        simp

end Omega.Conclusion

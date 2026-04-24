import Omega.Folding.DerivedFoldMultiplicityZerofiberEnvelope

namespace Omega.Folding

open scoped BigOperators

/-- Paper label: `cor:derived-fold-multiplicity-fibonacci-zerofiber-specialization`. -/
theorem paper_derived_fold_multiplicity_fibonacci_zerofiber_specialization {m : ℕ}
    (d : Fin (Nat.fib (m + 2) - Nat.fib ((m + 2) / 2)) → ℕ)
    (hvals :
      ∀ i,
        d i = 2 ^ m / (Nat.fib (m + 2) - Nat.fib ((m + 2) / 2)) ∨
          d i = 2 ^ m / (Nat.fib (m + 2) - Nat.fib ((m + 2) / 2)) + 1)
    (hsum : ∑ i, d i = 2 ^ m) :
    let n := Nat.fib (m + 2) - Nat.fib ((m + 2) / 2)
    let a := 2 ^ m / n
    let ρ := 2 ^ m % n
    (∑ i, d i ^ 2 = (n - ρ) * a ^ 2 + ρ * (a + 1) ^ 2) ∧
      (∀ T : ℕ, ∑ i, Nat.min (d i) T = (n - ρ) * Nat.min a T + ρ * Nat.min (a + 1) T) ∧
      (∃ i, d i = a + if ρ = 0 then 0 else 1) := by
  cases m with
  | zero =>
      exfalso
      simp at hsum
  | succ m =>
      have hF : 0 < Nat.fib (Nat.succ m + 2) := Nat.fib_pos.mpr (by omega)
      have hz : Nat.fib ((Nat.succ m + 2) / 2) < Nat.fib (Nat.succ m + 2) := by
        cases m with
        | zero =>
            native_decide
        | succ m =>
            have hlt :
                Nat.fib ((Nat.succ (Nat.succ m) + 2) / 2) <
                  Nat.fib (((Nat.succ (Nat.succ m) + 2) / 2) + 1) := by
              exact Nat.fib_lt_fib_succ (by omega)
            have hle :
                Nat.fib (((Nat.succ (Nat.succ m) + 2) / 2) + 1) ≤
                  Nat.fib (Nat.succ (Nat.succ m) + 2) := by
              exact Nat.fib_mono (by omega)
            exact lt_of_lt_of_le hlt hle
      have henv :=
        paper_derived_fold_multiplicity_zerofiber_envelope
          (F := Nat.fib (Nat.succ m + 2)) (M := 2 ^ Nat.succ m)
          (z := Nat.fib ((Nat.succ m + 2) / 2)) hF hz d hvals hsum
      dsimp only at henv ⊢
      rcases henv with ⟨hsq, -, hcap, htop⟩
      exact ⟨hsq, hcap, htop⟩

end Omega.Folding

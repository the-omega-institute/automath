import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-area-law-scalar-godel-incompatibility`. -/
theorem paper_conclusion_area_law_scalar_godel_incompatibility (b : ℕ) (q : Fin b → ℕ)
    (hq : ∀ i : Fin b, i.1 + 2 ≤ q i) : Nat.factorial (b + 1) ≤ ∏ i, q i := by
  induction b with
  | zero =>
      simp
  | succ b ih =>
      have htail : ∀ i : Fin b, i.1 + 2 ≤ q (Fin.castSucc i) := by
        intro i
        exact hq (Fin.castSucc i)
      have hprod : Nat.factorial (b + 1) ≤ ∏ i : Fin b, q (Fin.castSucc i) :=
        ih (fun i => q (Fin.castSucc i)) htail
      have hlast : b + 2 ≤ q (Fin.last b) := by
        simpa using hq (Fin.last b)
      calc
        Nat.factorial ((b + 1) + 1) = (b + 2) * Nat.factorial (b + 1) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.factorial_succ (b + 1))
        _ ≤ q (Fin.last b) * ∏ i : Fin b, q (Fin.castSucc i) :=
          Nat.mul_le_mul hlast hprod
        _ = ∏ i : Fin (b + 1), q i := by
          rw [Fin.prod_univ_castSucc]
          exact Nat.mul_comm _ _

end Omega.Conclusion

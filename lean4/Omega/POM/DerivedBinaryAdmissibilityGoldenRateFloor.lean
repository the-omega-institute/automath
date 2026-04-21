import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.WitnessExtractionOptimalSuccess

namespace Omega.POM

/-- Paper label: `cor:derived-binary-admissibility-golden-rate-floor`. Specialize the generic
witness-extraction success bound to the binary-admissible Fibonacci state count
`|X_m| = F_{m+2}`. -/
theorem paper_derived_binary_admissibility_golden_rate_floor (m B : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1)
    (hSucc : 1 - ε ≤ min (1 : ℝ) (((2 : ℝ) ^ B) / (Nat.fib (m + 2) : ℝ))) :
    (1 - ε) * (Nat.fib (m + 2) : ℝ) ≤ (2 : ℝ) ^ B := by
  have hFibPos : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
  let x : Fin (Nat.fib (m + 2)) := ⟨0, hFibPos⟩
  obtain ⟨Succ, hSuccDef, hBound⟩ :=
    paper_pom_witness_extraction_optimal_success
      (X := Fin (Nat.fib (m + 2)))
      (d := fun _ => Nat.fib (m + 2))
      (hd := fun _ => Nat.succ_le_of_lt hFibPos)
      B
  have hx : 1 - ε ≤ Succ x := by
    simpa [x, hSuccDef x] using hSucc
  exact hBound x ε hε0 hε1 hx

end Omega.POM

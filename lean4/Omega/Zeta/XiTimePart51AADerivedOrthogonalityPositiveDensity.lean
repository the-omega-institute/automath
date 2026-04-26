import Mathlib
import Omega.Zeta.XiTimePart51AADerivedCrossFibGcdFormula

namespace Omega.Zeta

/-- The concrete two-window seed model used to read the derived-cross gcd package on a pair of
windows. -/
def xi_time_part51aa_derived_orthogonality_positive_density_two_window_data
    (m n : ℕ) : XiDerivedCrossFibGcdFormulaData where
  windows := [m, n]

/-- The two-window derived-cross package identifies the Fibonacci gcd obstruction explicitly, so
coprime shifted windows force vanishing, and the classical comparison constant `6 / π²` is
positive. -/
def xi_time_part51aa_derived_orthogonality_positive_density_spec : Prop :=
  ∀ m n : ℕ,
    let D := xi_time_part51aa_derived_orthogonality_positive_density_two_window_data m n
    D.modulusGcd = Nat.fib (Nat.gcd (m + 2) (n + 2)) ∧
      (Nat.gcd (m + 2) (n + 2) = 1 → D.modulusGcd = 1) ∧
      (0 : ℝ) < 6 / Real.pi ^ 2

theorem paper_xi_time_part51aa_derived_orthogonality_positive_density :
    xi_time_part51aa_derived_orthogonality_positive_density_spec := by
  intro m n
  let D := xi_time_part51aa_derived_orthogonality_positive_density_two_window_data m n
  have hcollapse : D.fibGcdCollapse :=
    (paper_xi_time_part51aa_derived_cross_fib_gcd_formula D).2.1
  refine ⟨?_, ?_, by positivity⟩
  · simpa [D, xi_time_part51aa_derived_orthogonality_positive_density_two_window_data,
      XiDerivedCrossFibGcdFormulaData.fibGcdCollapse, XiDerivedCrossFibGcdFormulaData.indexGcd,
      XiDerivedCrossFibGcdFormulaData.shiftedWindows] using hcollapse
  · intro hcoprime
    calc
      D.modulusGcd = Nat.fib (Nat.gcd (m + 2) (n + 2)) := by
        simpa [D, xi_time_part51aa_derived_orthogonality_positive_density_two_window_data,
          XiDerivedCrossFibGcdFormulaData.fibGcdCollapse, XiDerivedCrossFibGcdFormulaData.indexGcd,
          XiDerivedCrossFibGcdFormulaData.shiftedWindows] using hcollapse
      _ = Nat.fib 1 := by rw [hcoprime]
      _ = 1 := by norm_num

end Omega.Zeta

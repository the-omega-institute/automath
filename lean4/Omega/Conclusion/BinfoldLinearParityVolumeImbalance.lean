import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.BinfoldGaugeCenterEventualTriviality
import Omega.Conclusion.FibonacciDistortionThreshold
import Omega.OperatorAlgebra.FoldGaugeGroupStructure
import Omega.Zeta.AuditedEvenFirstCapacityKinkFibonacciJump
import Omega.Zeta.XiTimePart65BinfoldGaugeCenterAbelianizationExact

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-binfold-linear-parity-volume-imbalance`.
The gauge center becomes trivial eventually, while on the audited even windows the abelianized
parity channel still has full Fibonacci cardinality. The resulting parity exponent is already
strictly below the dyadic volume scale on the first large audited windows. -/
theorem paper_conclusion_binfold_linear_parity_volume_imbalance :
    (∃ m0, ∀ m ≥ m0, ∀ z : binfoldGaugeCenter m, z = 1) ∧
      let N : (m : ℕ) → Fin (Nat.fib (m + 2)) → ℕ :=
        fun m w =>
          if w.1 < Nat.fib m then Omega.Zeta.auditedEvenFirstKink m else Omega.Zeta.auditedEvenFirstKink m + 1
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 8) = 2 ^ Nat.fib 10 ∧
        Omega.OperatorAlgebra.foldGaugeCenterOrder (N 8) = 1 ∧
        Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 10) = 2 ^ Nat.fib 12 ∧
        Omega.OperatorAlgebra.foldGaugeCenterOrder (N 10) = 1 ∧
        Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 12) = 2 ^ Nat.fib 14 ∧
        Omega.OperatorAlgebra.foldGaugeCenterOrder (N 12) = 1 ∧
      Nat.fib 10 < 2 ^ 8 ∧ Nat.fib 12 < 2 ^ 10 ∧ Nat.fib 14 < 2 ^ 12 := by
  rcases paper_conclusion_binfold_gauge_center_eventual_triviality with ⟨_, hCenter⟩
  dsimp
  let N : (m : ℕ) → Fin (Nat.fib (m + 2)) → ℕ :=
    fun m w =>
      if w.1 < Nat.fib m then Omega.Zeta.auditedEvenFirstKink m else Omega.Zeta.auditedEvenFirstKink m + 1
  have h8 :=
    Omega.Zeta.paper_xi_time_part65_binfold_gauge_center_abelianization_exact
      (m := Nat.fib 10) (fiber := N 8)
  have h10 :=
    Omega.Zeta.paper_xi_time_part65_binfold_gauge_center_abelianization_exact
      (m := Nat.fib 12) (fiber := N 10)
  have h12 :=
    Omega.Zeta.paper_xi_time_part65_binfold_gauge_center_abelianization_exact
      (m := Nat.fib 14) (fiber := N 12)
  have h8_ge2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 10) => 2 ≤ N 8 w).card = Nat.fib 10 := by
    native_decide
  have h10_ge2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 12) => 2 ≤ N 10 w).card = Nat.fib 12 := by
    native_decide
  have h12_ge2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 14) => 2 ≤ N 12 w).card = Nat.fib 14 := by
    native_decide
  have h8_eq2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 10) => N 8 w = 2).card = 0 := by
    native_decide
  have h10_eq2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 12) => N 10 w = 2).card = 0 := by
    native_decide
  have h12_eq2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 14) => N 12 w = 2).card = 0 := by
    native_decide
  have hAb8 :
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 8) = 2 ^ Nat.fib 10 := by
    simpa [h8_ge2] using h8.2
  have hAb10 :
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 10) = 2 ^ Nat.fib 12 := by
    simpa [h10_ge2] using h10.2
  have hAb12 :
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 12) = 2 ^ Nat.fib 14 := by
    simpa [h12_ge2] using h12.2
  have hCenter8' :
      Omega.OperatorAlgebra.foldGaugeCenterOrder (N 8) = 1 := by
    simpa [h8_eq2] using h8.1
  have hCenter10' :
      Omega.OperatorAlgebra.foldGaugeCenterOrder (N 10) = 1 := by
    simpa [h10_eq2] using h10.1
  have hCenter12' :
      Omega.OperatorAlgebra.foldGaugeCenterOrder (N 12) = 1 := by
    simpa [h12_eq2] using h12.1
  have hDist :=
    Omega.Conclusion.FibonacciDistortionThreshold.paper_conclusion_fibonacci_hard_distortion_threshold
  have hFib10 : Nat.fib 10 < 2 ^ 8 := by
    exact hDist.2.2.2.2.2.1
  have hFib12 : Nat.fib 12 < 2 ^ 10 := by
    native_decide
  have hFib14 : Nat.fib 14 < 2 ^ 12 := by
    native_decide
  simpa [N] using
    (show (∃ m0, ∀ m ≥ m0, ∀ z : binfoldGaugeCenter m, z = 1) ∧
        Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 8) = 2 ^ Nat.fib 10 ∧
        Omega.OperatorAlgebra.foldGaugeCenterOrder (N 8) = 1 ∧
        Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 10) = 2 ^ Nat.fib 12 ∧
        Omega.OperatorAlgebra.foldGaugeCenterOrder (N 10) = 1 ∧
        Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 12) = 2 ^ Nat.fib 14 ∧
        Omega.OperatorAlgebra.foldGaugeCenterOrder (N 12) = 1 ∧
        Nat.fib 10 < 2 ^ 8 ∧ Nat.fib 12 < 2 ^ 10 ∧ Nat.fib 14 < 2 ^ 12 from
      ⟨hCenter, hAb8, hCenter8', hAb10, hCenter10', hAb12, hCenter12', hFib10, hFib12, hFib14⟩)

end Omega.Conclusion

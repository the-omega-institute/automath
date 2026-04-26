import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldGaugeGroupStructure
import Omega.Zeta.AuditedEvenFirstCapacityKinkFibonacciJump
import Omega.Zeta.XiTimePart65BinfoldGaugeCenterAbelianizationExact

namespace Omega.Zeta

open scoped BigOperators

/-- Audited-even fiber multiplicity model: `F_m` fibers of size `F_{m/2}` and `F_{m+1}` fibers of
size `F_{m/2} + 1`, indexed on `Fin (F_{m+2})`. -/
def xi_foldbin_even_window_parity_section_center_intersection_multiplicity (m : ℕ) :
    Fin (Nat.fib (m + 2)) → ℕ :=
  fun w =>
    if w.1 < Nat.fib m then auditedEvenFirstKink m else auditedEvenFirstKink m + 1

/-- The number of audited-even fibers of multiplicity exactly `2`. -/
def xi_foldbin_even_window_parity_section_center_intersection_B (m : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin (Nat.fib (m + 2)) =>
    xi_foldbin_even_window_parity_section_center_intersection_multiplicity m w = 2).card

/-- Paper label: `thm:xi-foldbin-even-window-parity-section-center-intersection`.
In the audited even-window model, every fiber contributes one `C₂` to the abelianized parity
section, while the intersection with the center comes only from the multiplicity-`2` sector.
The audited counts are `B₆ = 8` and `B₈ = B₁₀ = B₁₂ = 0`. -/
theorem paper_xi_foldbin_even_window_parity_section_center_intersection :
    let N := xi_foldbin_even_window_parity_section_center_intersection_multiplicity
    let B := xi_foldbin_even_window_parity_section_center_intersection_B
    Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 6) = 2 ^ Nat.fib 8 ∧
      Omega.OperatorAlgebra.foldGaugeCenterOrder (N 6) = 2 ^ B 6 ∧
      B 6 = 8 ∧
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 8) = 2 ^ Nat.fib 10 ∧
      Omega.OperatorAlgebra.foldGaugeCenterOrder (N 8) = 2 ^ B 8 ∧
      B 8 = 0 ∧
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 10) = 2 ^ Nat.fib 12 ∧
      Omega.OperatorAlgebra.foldGaugeCenterOrder (N 10) = 2 ^ B 10 ∧
      B 10 = 0 ∧
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (N 12) = 2 ^ Nat.fib 14 ∧
      Omega.OperatorAlgebra.foldGaugeCenterOrder (N 12) = 2 ^ B 12 ∧
      B 12 = 0 := by
  dsimp
  have h6 :=
    paper_xi_time_part65_binfold_gauge_center_abelianization_exact
      (m := Nat.fib 8)
      (fiber := xi_foldbin_even_window_parity_section_center_intersection_multiplicity 6)
  have h8 :=
    paper_xi_time_part65_binfold_gauge_center_abelianization_exact
      (m := Nat.fib 10)
      (fiber := xi_foldbin_even_window_parity_section_center_intersection_multiplicity 8)
  have h10 :=
    paper_xi_time_part65_binfold_gauge_center_abelianization_exact
      (m := Nat.fib 12)
      (fiber := xi_foldbin_even_window_parity_section_center_intersection_multiplicity 10)
  have h12 :=
    paper_xi_time_part65_binfold_gauge_center_abelianization_exact
      (m := Nat.fib 14)
      (fiber := xi_foldbin_even_window_parity_section_center_intersection_multiplicity 12)
  have h6_ge2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 8) =>
        2 ≤ xi_foldbin_even_window_parity_section_center_intersection_multiplicity 6 w).card =
        Nat.fib 8 := by
    native_decide
  have h8_ge2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 10) =>
        2 ≤ xi_foldbin_even_window_parity_section_center_intersection_multiplicity 8 w).card =
        Nat.fib 10 := by
    native_decide
  have h10_ge2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 12) =>
        2 ≤ xi_foldbin_even_window_parity_section_center_intersection_multiplicity 10 w).card =
        Nat.fib 12 := by
    native_decide
  have h12_ge2 :
      (Finset.univ.filter fun w : Fin (Nat.fib 14) =>
        2 ≤ xi_foldbin_even_window_parity_section_center_intersection_multiplicity 12 w).card =
        Nat.fib 14 := by
    native_decide
  have hB6 :
      xi_foldbin_even_window_parity_section_center_intersection_B 6 = 8 := by
    native_decide
  have hB8 :
      xi_foldbin_even_window_parity_section_center_intersection_B 8 = 0 := by
    native_decide
  have hB10 :
      xi_foldbin_even_window_parity_section_center_intersection_B 10 = 0 := by
    native_decide
  have hB12 :
      xi_foldbin_even_window_parity_section_center_intersection_B 12 = 0 := by
    native_decide
  refine ⟨?_, ?_, hB6, ?_, ?_, hB8, ?_, ?_, hB10, ?_, ?_, hB12⟩
  · simpa [h6_ge2] using h6.2
  · simpa [xi_foldbin_even_window_parity_section_center_intersection_B, hB6] using h6.1
  · simpa [h8_ge2] using h8.2
  · simpa [xi_foldbin_even_window_parity_section_center_intersection_B, hB8] using h8.1
  · simpa [h10_ge2] using h10.2
  · simpa [xi_foldbin_even_window_parity_section_center_intersection_B, hB10] using h10.1
  · simpa [h12_ge2] using h12.2
  · simpa [xi_foldbin_even_window_parity_section_center_intersection_B, hB12] using h12.1

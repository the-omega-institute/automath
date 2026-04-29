import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-schur-signature-parseval-simplex`. Character-column
orthogonality gives the finite Parseval identity for the Schur signature transform. -/
theorem paper_conclusion_schur_signature_parseval_simplex {Lam Nu : Type*} [Fintype Lam]
    [Fintype Nu] [DecidableEq Nu] (chi : Lam → Nu → ℂ) (z a b : Nu → ℂ)
    (horth :
      ∀ μ ν, (∑ l : Lam, chi l μ * star (chi l ν)) = if μ = ν then z μ else 0) :
    (∑ l : Lam, (∑ ν : Nu, a ν * chi l ν) * star (∑ ν : Nu, b ν * chi l ν)) =
      ∑ ν : Nu, z ν * a ν * star (b ν) := by
  classical
  calc
    (∑ l : Lam, (∑ ν : Nu, a ν * chi l ν) * star (∑ ν : Nu, b ν * chi l ν)) =
        ∑ l : Lam, ∑ μ : Nu, ∑ ν : Nu,
          (a ν * star (b μ)) * (chi l ν * star (chi l μ)) := by
      refine Finset.sum_congr rfl ?_
      intro l _
      simp [Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ μ : Nu, ∑ ν : Nu, ∑ l : Lam,
          (a ν * star (b μ)) * (chi l ν * star (chi l μ)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro μ _
      rw [Finset.sum_comm]
    _ = ∑ ν : Nu, ∑ μ : Nu, ∑ l : Lam,
          (a ν * star (b μ)) * (chi l ν * star (chi l μ)) := by
      rw [Finset.sum_comm]
    _ = ∑ ν : Nu, ∑ μ : Nu,
          (a ν * star (b μ)) * (∑ l : Lam, chi l ν * star (chi l μ)) := by
      simp [Finset.mul_sum]
    _ = ∑ ν : Nu, ∑ μ : Nu,
          (a ν * star (b μ)) * (if ν = μ then z ν else 0) := by
      refine Finset.sum_congr rfl ?_
      intro ν _
      refine Finset.sum_congr rfl ?_
      intro μ _
      rw [horth ν μ]
    _ = ∑ ν : Nu, z ν * a ν * star (b ν) := by
      simp [mul_assoc, mul_left_comm, mul_comm]

end Omega.Conclusion

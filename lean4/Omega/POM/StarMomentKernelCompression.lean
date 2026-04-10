import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Symmetric tensor subspace dimension: dim Sym^{q-1}(V) = C(k+q-2, q-1).
    Paper: `thm:pom-star-moment-kernel-perron-symmetric-compression`. -/
theorem star_moment_dim_k3_q2 : Nat.choose 3 1 = 3 := by native_decide

theorem star_moment_dim_k3_q3 : Nat.choose 4 2 = 6 := by native_decide

theorem star_moment_dim_k3_q4 : Nat.choose 5 3 = 10 := by native_decide

theorem star_moment_dim_k3_q5 : Nat.choose 6 4 = 15 := by native_decide

/-- For k=3, C(q+1, 2) = C(q+1, q-1) by symmetry of binomial coefficients. -/
theorem star_moment_k3_identity (q : Nat) (hq : q ≥ 2) :
    Nat.choose (q + 1) 2 = Nat.choose (q + 1) (q - 1) := by
  rw [show q - 1 = q + 1 - 2 from by omega, Nat.choose_symm (by omega : 2 ≤ q + 1)]

/-- Paper: `thm:pom-star-moment-kernel-perron-symmetric-compression`.
    Seed package: k=3 triangular number formula seeds + dimension identity. -/
theorem paper_pom_star_moment_kernel_compression_seeds :
    Nat.choose 3 1 = 3 ∧
    Nat.choose 4 2 = 6 ∧
    Nat.choose 5 3 = 10 ∧
    Nat.choose 6 4 = 15 ∧
    Nat.choose 7 5 = 21 ∧
    Nat.choose 8 6 = 28 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end Omega.POM

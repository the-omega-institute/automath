import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

namespace Omega.Zeta

open BigOperators Matrix Polynomial

/-- thm:zeta-syntax-trace-linear-recurrence -/
theorem paper_zeta_syntax_trace_linear_recurrence {d : Nat} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    ∃ c : Fin d → ℂ, ∀ n : Nat,
      (A ^ (n + d)).trace + ∑ i : Fin d, c i * (A ^ (n + i.val)).trace = 0 := by
  classical
  let _ : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine ⟨fun i => A.charpoly.coeff i.val, ?_⟩
  intro n
  have hdeg : A.charpoly.natDegree = d := by
    simp
  have hpoly :
      A.charpoly =
        X ^ d + ∑ i ∈ Finset.range d, C (A.charpoly.coeff i) * X ^ i := by
    simpa [hdeg] using A.charpoly_monic.as_sum
  have hCH : aeval A A.charpoly = 0 := Matrix.aeval_self_charpoly A
  rw [hpoly] at hCH
  simp only [map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C] at hCH
  have hmul := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => A ^ n * M) hCH
  simp [mul_add, Finset.mul_sum, Algebra.algebraMap_eq_smul_one, ← pow_add] at hmul
  have htrace := congrArg Matrix.trace hmul
  rw [← Fin.sum_univ_eq_sum_range] at htrace
  simpa using htrace

end Omega.Zeta

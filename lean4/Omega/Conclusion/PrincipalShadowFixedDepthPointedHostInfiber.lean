import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-principal-shadow-fixed-depth-pointed-host-infiber`.
A homogeneous real linear system with more unknowns than equations has a nonzero solution. -/
theorem paper_conclusion_principal_shadow_fixed_depth_pointed_host_infiber (n N : ℕ)
    (hN : 2 * n < N) (A : Fin (2 * n) → Fin N → ℝ) :
    ∃ c : Fin N → ℝ, (∃ j, c j ≠ 0) ∧ ∀ i, (∑ j, A i j * c j) = 0 := by
  let L : (Fin N → ℝ) →ₗ[ℝ] (Fin (2 * n) → ℝ) :=
    { toFun := fun c => fun i => ∑ j, A i j * c j
      map_add' := by
        intro c d
        ext i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        ext i
        simp [Finset.mul_sum, mul_left_comm] }
  have hrange_le : Module.finrank ℝ L.range ≤ 2 * n := by
    calc
      Module.finrank ℝ L.range ≤ Module.finrank ℝ (Fin (2 * n) → ℝ) :=
        Submodule.finrank_le L.range
      _ = 2 * n := Module.finrank_fin_fun (R := ℝ)
  have hker_pos : 0 < Module.finrank ℝ L.ker := by
    have hsum := L.finrank_range_add_finrank_ker
    have hdomain : Module.finrank ℝ (Fin N → ℝ) = N := Module.finrank_fin_fun (R := ℝ)
    omega
  haveI : Nontrivial L.ker := Module.finrank_pos_iff.mp hker_pos
  obtain ⟨v, hv⟩ := exists_ne (0 : L.ker)
  refine ⟨v, ?_, ?_⟩
  · by_contra hzero
    apply hv
    ext j
    by_contra hj
    exact hzero ⟨j, hj⟩
  · intro i
    change (L (v : Fin N → ℝ)) i = 0
    exact congrFun (LinearMap.mem_ker.mp v.property) i

end Omega.Conclusion

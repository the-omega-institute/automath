import Mathlib.Tactic
import Omega.POM.LocalDefectGibbsVariational

namespace Omega.POM

open scoped BigOperators

/-- The arithmetic mean of the local fiber sizes. -/
noncomputable def pom_small_defect_fiber_rigidity_arithmetic_mean {k : ℕ}
    (n : Fin (k + 1) → ℕ) : ℝ :=
  pom_local_defect_gibbs_variational_total_mass n / (k + 1 : ℝ)

/-- Paper label: `cor:pom-small-defect-fiber-rigidity`. Once the local AM/GM defect is identified
with the KL divergence from the uniform law to the normalized fiber-size law, any Pinsker-style
`L¹` bound turns into a coordinatewise control of the ratios `nᵢ / AM_z`. -/
theorem paper_pom_small_defect_fiber_rigidity
    (D : pom_local_defect_gibbs_variational_data)
    (hPinsker :
      ∑ i,
          |pom_local_defect_gibbs_variational_uniform_law D.k i -
              pom_local_defect_gibbs_variational_size_biased_law D.fiber_size i| ≤
        Real.sqrt
          (2 *
            pom_local_defect_gibbs_variational_kl_div
              (pom_local_defect_gibbs_variational_uniform_law D.k)
              (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size))) :
    ∀ i : Fin (D.k + 1),
      |(D.fiber_size i : ℝ) / pom_small_defect_fiber_rigidity_arithmetic_mean D.fiber_size - 1| ≤
        (D.k + 1 : ℝ) *
          Real.sqrt (2 * pom_local_defect_gibbs_variational_defect D.k D.fiber_size) := by
  let u : Fin (D.k + 1) → ℝ := pom_local_defect_gibbs_variational_uniform_law D.k
  let q : Fin (D.k + 1) → ℝ := pom_local_defect_gibbs_variational_size_biased_law D.fiber_size
  have hkl_defect :
      pom_local_defect_gibbs_variational_kl_div u q =
        pom_local_defect_gibbs_variational_defect D.k D.fiber_size := by
    simpa [u, q] using (paper_pom_local_defect_gibbs_variational D).2.1.symm
  have hk_pos : 0 < (D.k + 1 : ℝ) := by positivity
  have htotal_pos :
      0 < pom_local_defect_gibbs_variational_total_mass D.fiber_size := by
    unfold pom_local_defect_gibbs_variational_total_mass
    let i0 : Fin (D.k + 1) := ⟨0, Nat.succ_pos _⟩
    have hi0_pos : 0 < (D.fiber_size i0 : ℝ) := by
      exact_mod_cast D.fiber_size_pos i0
    have hi0_le :
        (D.fiber_size i0 : ℝ) ≤ ∑ i, (D.fiber_size i : ℝ) := by
      simpa [i0] using
        (Finset.single_le_sum
          (f := fun i : Fin (D.k + 1) => (D.fiber_size i : ℝ))
          (fun j _ => by positivity)
          (by simpa [i0] using (Finset.mem_univ i0)))
    exact lt_of_lt_of_le hi0_pos hi0_le
  intro i
  have hcoord :
      |u i - q i| ≤ ∑ j, |u j - q j| := by
    simpa [u, q] using
      (Finset.single_le_sum
        (f := fun j : Fin (D.k + 1) => |u j - q j|)
        (fun j _ => abs_nonneg _)
        (Finset.mem_univ i))
  have hsum_bound :
      ∑ j, |u j - q j| ≤
        Real.sqrt (2 * pom_local_defect_gibbs_variational_defect D.k D.fiber_size) := by
    simpa [u, q, hkl_defect] using hPinsker
  have hratio :
      (D.fiber_size i : ℝ) / pom_small_defect_fiber_rigidity_arithmetic_mean D.fiber_size - 1 =
        (D.k + 1 : ℝ) * (q i - u i) := by
    dsimp [pom_small_defect_fiber_rigidity_arithmetic_mean, u, q,
      pom_local_defect_gibbs_variational_uniform_law,
      pom_local_defect_gibbs_variational_size_biased_law]
    field_simp [htotal_pos.ne', hk_pos.ne']
  calc
    |(D.fiber_size i : ℝ) / pom_small_defect_fiber_rigidity_arithmetic_mean D.fiber_size - 1|
        = |(D.k + 1 : ℝ) * (q i - u i)| := by rw [hratio]
    _ = (D.k + 1 : ℝ) * |q i - u i| := by
      rw [abs_mul, abs_of_nonneg hk_pos.le]
    _ = (D.k + 1 : ℝ) * |u i - q i| := by rw [abs_sub_comm]
    _ ≤ (D.k + 1 : ℝ) * ∑ j, |u j - q j| := by
      exact mul_le_mul_of_nonneg_left hcoord hk_pos.le
    _ ≤ (D.k + 1 : ℝ) *
          Real.sqrt (2 * pom_local_defect_gibbs_variational_defect D.k D.fiber_size) := by
      exact mul_le_mul_of_nonneg_left hsum_bound hk_pos.le

end Omega.POM

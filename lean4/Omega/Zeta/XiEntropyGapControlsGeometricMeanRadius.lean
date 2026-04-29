import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic
import Omega.Zeta.XiEntropyGapExponentialSuppressionNonzeroFingerprint

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:xi-entropy-gap-controls-geometric-mean-radius`. -/
theorem paper_xi_entropy_gap_controls_geometric_mean_radius {κ : ℕ} (mass δ : Fin κ → ℝ)
    (hm : ∀ j, 0 ≤ mass j) (hδ : ∀ j, 0 < δ j) (hmass : 0 < xiIndexMass mass) :
    Real.exp (-(∑ j, mass j * (1 + δ j)) / xiIndexMass mass) ≤
      Real.exp (-1) * xiEntropyGap mass δ / xiIndexMass mass := by
  let K : ℝ := xiIndexMass mass
  have hK_pos : 0 < K := hmass
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hweights_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin κ)), 0 ≤ mass j / K := by
    intro j _
    exact div_nonneg (hm j) hK_pos.le
  have hweights_sum : ∑ j ∈ (Finset.univ : Finset (Fin κ)), mass j / K = 1 := by
    calc
      ∑ j ∈ (Finset.univ : Finset (Fin κ)), mass j / K = (∑ j, mass j) / K := by
        rw [Finset.sum_div]
      _ = 1 := by
        rw [show (∑ j, mass j) = K by simp [K, xiIndexMass]]
        exact div_self hK_ne
  have hJensen :=
    convexOn_exp.map_sum_le (t := (Finset.univ : Finset (Fin κ))) (w := fun j => mass j / K)
      (p := fun j => -(1 + δ j)) hweights_nonneg hweights_sum (fun _ _ => Set.mem_univ _)
  have hpointwise :
      ∀ j : Fin κ, (mass j / K) * Real.exp (-(1 + δ j)) ≤ (mass j / K) * (Real.exp (-1) / (1 + δ j)) := by
    intro j
    have hbase : Real.exp (-(δ j)) ≤ (1 + δ j)⁻¹ := by
      simpa using exp_neg_mul_nat_le_inv_one_add (δ j) (hδ j) (n := 1) (by norm_num)
    have hrewrite : Real.exp (-(1 + δ j)) = Real.exp (-1) * Real.exp (-(δ j)) := by
      rw [show -(1 + δ j) = (-1 : ℝ) + (-δ j) by ring, Real.exp_add]
    rw [hrewrite]
    have hscale_nonneg : 0 ≤ (mass j / K) * Real.exp (-1) := by
      exact mul_nonneg (div_nonneg (hm j) hK_pos.le) (by positivity)
    have := mul_le_mul_of_nonneg_left hbase hscale_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using this
  have hsum_bound :
      ∑ j, (mass j / K) * Real.exp (-(1 + δ j)) ≤ Real.exp (-1) * xiEntropyGap mass δ / K := by
    calc
      ∑ j, (mass j / K) * Real.exp (-(1 + δ j))
          ≤ ∑ j, (mass j / K) * (Real.exp (-1) / (1 + δ j)) := by
              refine Finset.sum_le_sum ?_
              intro j _
              exact hpointwise j
      _ = Real.exp (-1) * xiEntropyGap mass δ / K := by
        calc
          ∑ j, (mass j / K) * (Real.exp (-1) / (1 + δ j))
              = ∑ j, Real.exp (-1) * ((mass j / (1 + δ j)) / K) := by
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  have hden_ne : (1 + δ j) ≠ 0 := by linarith [hδ j]
                  field_simp [hK_ne, hden_ne]
          _ = Real.exp (-1) * ∑ j, (mass j / (1 + δ j)) / K := by rw [Finset.mul_sum]
          _ = Real.exp (-1) * ((∑ j, mass j / (1 + δ j)) / K) := by rw [← Finset.sum_div]
          _ = Real.exp (-1) * xiEntropyGap mass δ / K := by
                rw [xiEntropyGap]
                field_simp [hK_ne]
  have hleft :
      ∑ j, (mass j / K) * (-(1 + δ j)) = -(∑ j, mass j * (1 + δ j)) / K := by
    calc
      ∑ j, (mass j / K) * (-(1 + δ j)) = ∑ j, (-(mass j * (1 + δ j))) / K := by
            refine Finset.sum_congr rfl ?_
            intro j _
            field_simp [hK_ne]
      _ = (∑ j, -(mass j * (1 + δ j))) / K := by rw [Finset.sum_div]
      _ = -(∑ j, mass j * (1 + δ j)) / K := by rw [Finset.sum_neg_distrib]
  calc
    Real.exp (-(∑ j, mass j * (1 + δ j)) / xiIndexMass mass)
        = Real.exp (-(∑ j, mass j * (1 + δ j)) / K) := by rfl
    _ = Real.exp (∑ j, (mass j / K) * (-(1 + δ j))) := by rw [hleft.symm]
    _ ≤ ∑ j, (mass j / K) * Real.exp (-(1 + δ j)) := by
          simpa [smul_eq_mul] using hJensen
    _ ≤ Real.exp (-1) * xiEntropyGap mass δ / K := hsum_bound
    _ = Real.exp (-1) * xiEntropyGap mass δ / xiIndexMass mass := by rfl

end Omega.Zeta

import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.Entropy

open scoped goldenRatio
open Filter Topology

namespace Omega.Zeta

/-- Exact number of admissible level-`n` cylinders in the Gödel--Zeckendorf limit model. -/
def xi_time_part62d_zg_critical_hausdorff_measure_coverCount (n : ℕ) : ℕ :=
  Nat.fib (n + 2)

/-- Exact `s_B`-content at scale `B^{-n}` after using `B^{s_B} = φ`. -/
noncomputable def xi_time_part62d_zg_critical_hausdorff_measure_content (n : ℕ) : ℝ :=
  (xi_time_part62d_zg_critical_hausdorff_measure_coverCount n : ℝ) * φ ^ (-(n : ℝ))

/-- The critical Hausdorff-measure constant predicted by the Fibonacci/Binet scaling. -/
noncomputable def xi_time_part62d_zg_critical_hausdorff_measure_limit : ℝ :=
  φ ^ (2 : ℕ) / Real.sqrt 5

/-- Paper label: `thm:xi-time-part62d-zg-critical-hausdorff-measure`. At scale `B^{-n}`, the
canonical cylinder cover has exactly `F_{n+2}` pieces, so the exact `s_B`-content is
`F_{n+2} B^{-n s_B} = F_{n+2} φ^{-n}`, and Binet gives the limit `φ^2 / √5`. -/
theorem paper_xi_time_part62d_zg_critical_hausdorff_measure :
    (∀ n : ℕ,
      xi_time_part62d_zg_critical_hausdorff_measure_coverCount n = Nat.fib (n + 2)) ∧
      (∀ n : ℕ,
      xi_time_part62d_zg_critical_hausdorff_measure_content n =
          (Nat.fib (n + 2) : ℝ) * φ ^ (-(n : ℝ))) ∧
      Tendsto xi_time_part62d_zg_critical_hausdorff_measure_content atTop
        (nhds xi_time_part62d_zg_critical_hausdorff_measure_limit) := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  have hshift :=
    Omega.Entropy.fib_mul_phi_neg_tendsto_inv_sqrt5.comp (tendsto_add_atTop_nat 2)
  have hmul :
      Tendsto (fun n : ℕ => ((Nat.fib (n + 2) : ℝ) * φ ^ (-(n + 2 : ℝ))) * φ ^ (2 : ℕ)) atTop
        (nhds ((Real.sqrt 5)⁻¹ * φ ^ (2 : ℕ))) := by
    simpa [Function.comp] using hshift.mul tendsto_const_nhds
  have hevent :
      (fun n : ℕ => xi_time_part62d_zg_critical_hausdorff_measure_content n) =ᶠ[atTop]
        fun n => ((Nat.fib (n + 2) : ℝ) * φ ^ (-(n + 2 : ℝ))) * φ ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun n => by
      unfold xi_time_part62d_zg_critical_hausdorff_measure_content
        xi_time_part62d_zg_critical_hausdorff_measure_coverCount
      have hpow :
          φ ^ (-(n : ℝ)) = φ ^ (-(n + 2 : ℝ)) * φ ^ (2 : ℝ) := by
        rw [show (-(n : ℝ)) = (-(n + 2 : ℝ)) + (2 : ℝ) by norm_num]
        exact Real.rpow_add Real.goldenRatio_pos (-(n + 2 : ℝ)) (2 : ℝ)
      calc
        (Nat.fib (n + 2) : ℝ) * φ ^ (-(n : ℝ))
            = (Nat.fib (n + 2) : ℝ) * (φ ^ (-(n + 2 : ℝ)) * φ ^ (2 : ℕ)) := by
                simpa [Real.rpow_natCast] using congrArg ((Nat.fib (n + 2) : ℝ) * ·) hpow
        _ = ((Nat.fib (n + 2) : ℝ) * φ ^ (-(n + 2 : ℝ))) * φ ^ (2 : ℕ) := by ring
  refine Filter.Tendsto.congr' hevent.symm ?_
  simpa [xi_time_part62d_zg_critical_hausdorff_measure_limit, one_div, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hmul

end Omega.Zeta

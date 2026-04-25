import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Conclusion.TqftGenusHausdorffMomentSequence

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `prop:conclusion-tqft-genus-logconvexity`. For the normalized genus partition
sequence attached to the concrete fiber multiplicities, the midpoint log-convexity inequality
`Z₁² ≤ Z₀ Z₂` is the finite Cauchy-Schwarz inequality for the node list `d_m(x)⁻²`. -/
theorem paper_conclusion_tqft_genus_logconvexity
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) :
    let Z := D.conclusion_tqft_genus_hausdorff_moment_sequence_partition
    Z 1 ^ 2 ≤ Z 0 * Z 2 := by
  dsimp
  let a : Fin D.n → ℝ := fun x => D.conclusion_tqft_genus_hausdorff_moment_sequence_node x
  let s : ℝ := ∑ x : Fin D.n, a x
  let t : ℝ := ∑ x : Fin D.n, a x ^ 2
  have hn_pos : (0 : ℝ) < D.n := by
    exact_mod_cast D.conclusion_tqft_genus_hausdorff_moment_sequence_nonempty
  have hn_ne : (D.n : ℝ) ≠ 0 := by
    positivity
  have hsq :
      s ^ 2 ≤ (D.n : ℝ) * t := by
    simpa [a, s, t] using
      (Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (s := Finset.univ)
        (fun _ : Fin D.n => (1 : ℝ)) a)
  have hineq : s * s / (D.n * D.n) ≤ t / D.n := by
    field_simp [hn_ne]
    nlinarith [hsq]
  simpa [conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_partition,
    a, s, t, pow_two, hn_ne, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hineq

end Omega.Conclusion

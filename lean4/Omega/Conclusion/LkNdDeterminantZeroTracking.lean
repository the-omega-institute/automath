import Mathlib
import Omega.Conclusion.LkFixedIndexHardEdge

namespace Omega.Conclusion

open Filter
open scoped BigOperators

noncomputable section

/-- The explicit finite zero location coming from the `p`-th hard-edge eigenvalue. -/
def conclusion_lk_nd_determinant_zero_tracking_zero_location (k p : ℕ) : ℝ :=
  -(((2 * k + 1 : ℝ) ^ 2) / 4) * conclusion_lk_fixed_index_hard_edge_eigenvalue k p

/-- The limiting `p`-th zero of the `cosh (sqrt s)` model, indexed from `p = 0`. -/
def conclusion_lk_nd_determinant_zero_tracking_limit_zero (p : ℕ) : ℝ :=
  -(((2 * p - 1 : ℝ) ^ 2) * Real.pi ^ 2 / 4)

/-- The determinant family is recorded by its finite spectral product. -/
structure conclusion_lk_nd_determinant_zero_tracking_data where
  determinant : ℕ → ℝ → ℝ
  h_det :
    ∀ k : ℕ, ∀ s : ℝ,
      determinant k s =
        Finset.prod (Finset.range k) fun p =>
          (conclusion_lk_fixed_index_hard_edge_eigenvalue k p +
            4 * s / ((2 * k + 1 : ℝ) ^ 2))
  h_local_uniform :
    Tendsto determinant atTop (nhds fun s : ℝ => Real.cosh (Real.sqrt s))

namespace conclusion_lk_nd_determinant_zero_tracking_data

/-- The packaged zero-tracking statement. -/
def holds (D : conclusion_lk_nd_determinant_zero_tracking_data) : Prop :=
  Tendsto D.determinant atTop (nhds fun s : ℝ => Real.cosh (Real.sqrt s)) ∧
    (∀ k p : ℕ, p < k →
      D.determinant k (conclusion_lk_nd_determinant_zero_tracking_zero_location k p) = 0) ∧
    (∀ p : ℕ,
      Tendsto
        (fun k : ℕ => conclusion_lk_nd_determinant_zero_tracking_zero_location (k + p + 1) p)
        atTop (nhds (conclusion_lk_nd_determinant_zero_tracking_limit_zero p))) ∧
    ∀ p : ℕ,
      conclusion_lk_nd_determinant_zero_tracking_limit_zero p =
        -(((2 * p - 1 : ℝ) ^ 2) * Real.pi ^ 2 / 4)

end conclusion_lk_nd_determinant_zero_tracking_data

/-- The finite zero locations simplify exactly to the limiting `cosh (sqrt s)` zero lattice. -/
lemma conclusion_lk_nd_determinant_zero_tracking_zero_location_eq_limit_zero (k p : ℕ) :
    conclusion_lk_nd_determinant_zero_tracking_zero_location k p =
      conclusion_lk_nd_determinant_zero_tracking_limit_zero p := by
  unfold conclusion_lk_nd_determinant_zero_tracking_zero_location
    conclusion_lk_nd_determinant_zero_tracking_limit_zero
    conclusion_lk_fixed_index_hard_edge_eigenvalue
  have hk : ((2 * k + 1 : ℝ) ^ 2) ≠ 0 := by positivity
  field_simp [hk]

open conclusion_lk_nd_determinant_zero_tracking_data

/-- Paper label: `thm:conclusion-Lk-nd-determinant-zero-tracking`. The local-uniform determinant
limit is supplied in the data, the finite zeros are the explicit hard-edge spectral roots of the
determinant product, and the fixed-index hard-edge law identifies their limiting lattice. -/
theorem paper_conclusion_lk_nd_determinant_zero_tracking
    (D : conclusion_lk_nd_determinant_zero_tracking_data) : D.holds := by
  refine ⟨D.h_local_uniform, ?_, ?_, ?_⟩
  · intro k p hp
    rw [D.h_det k (conclusion_lk_nd_determinant_zero_tracking_zero_location k p)]
    classical
    refine Finset.prod_eq_zero_iff.mpr ?_
    refine ⟨p, Finset.mem_range.mpr hp, ?_⟩
    unfold conclusion_lk_nd_determinant_zero_tracking_zero_location
    have hk : ((2 * k + 1 : ℝ) ^ 2) ≠ 0 := by positivity
    field_simp [conclusion_lk_fixed_index_hard_edge_eigenvalue, hk]
    ring
  · intro p
    have hconst :
        (fun k : ℕ =>
          conclusion_lk_nd_determinant_zero_tracking_zero_location (k + p + 1) p) =
          fun _ : ℕ => conclusion_lk_nd_determinant_zero_tracking_limit_zero p := by
      funext k
      exact conclusion_lk_nd_determinant_zero_tracking_zero_location_eq_limit_zero (k + p + 1) p
    rw [hconst]
    exact tendsto_const_nhds
  · intro p
    rfl

end

end Omega.Conclusion

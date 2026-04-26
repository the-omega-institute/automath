import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Finite fixed-resolution log-partition function after writing log weights as `a`. -/
def conclusion_fixedresolution_logpartition_escort_convexity_partition
    {ι : Type} [Fintype ι] (a : ι → ℝ) (q : ℝ) : ℝ :=
  ∑ x, Real.exp (q * a x)

/-- Escort probability at parameter `q`. -/
def conclusion_fixedresolution_logpartition_escort_convexity_escort
    {ι : Type} [Fintype ι] (a : ι → ℝ) (q : ℝ) (x : ι) : ℝ :=
  Real.exp (q * a x) /
    conclusion_fixedresolution_logpartition_escort_convexity_partition a q

/-- Escort expectation of the log weights. -/
def conclusion_fixedresolution_logpartition_escort_convexity_mean
    {ι : Type} [Fintype ι] (a : ι → ℝ) (q : ℝ) : ℝ :=
  ∑ x, conclusion_fixedresolution_logpartition_escort_convexity_escort a q x * a x

/-- The numerator-over-partition expression obtained by differentiating the log partition. -/
def conclusion_fixedresolution_logpartition_escort_convexity_first_derivative
    {ι : Type} [Fintype ι] (a : ι → ℝ) (q : ℝ) : ℝ :=
  (∑ x, Real.exp (q * a x) * a x) /
    conclusion_fixedresolution_logpartition_escort_convexity_partition a q

/-- Escort variance of the log weights. -/
def conclusion_fixedresolution_logpartition_escort_convexity_variance
    {ι : Type} [Fintype ι] (a : ι → ℝ) (q : ℝ) : ℝ :=
  ∑ x,
    conclusion_fixedresolution_logpartition_escort_convexity_escort a q x *
      (a x - conclusion_fixedresolution_logpartition_escort_convexity_mean a q) ^ (2 : ℕ)

/-- The second-derivative expression of finite log-sum-exp, written as escort variance. -/
def conclusion_fixedresolution_logpartition_escort_convexity_second_derivative
    {ι : Type} [Fintype ι] (a : ι → ℝ) (q : ℝ) : ℝ :=
  conclusion_fixedresolution_logpartition_escort_convexity_variance a q

/-- Nonconstant log weights at the fixed resolution. -/
def conclusion_fixedresolution_logpartition_escort_convexity_nonconstant
    {ι : Type} (a : ι → ℝ) : Prop :=
  ∃ x y, a x ≠ a y

lemma conclusion_fixedresolution_logpartition_escort_convexity_partition_pos
    {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (q : ℝ) :
    0 < conclusion_fixedresolution_logpartition_escort_convexity_partition a q := by
  classical
  unfold conclusion_fixedresolution_logpartition_escort_convexity_partition
  exact Finset.sum_pos (fun x _ => Real.exp_pos (q * a x))
    Finset.univ_nonempty

lemma conclusion_fixedresolution_logpartition_escort_convexity_escort_pos
    {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (q : ℝ) (x : ι) :
    0 < conclusion_fixedresolution_logpartition_escort_convexity_escort a q x := by
  exact div_pos (Real.exp_pos _) <|
    conclusion_fixedresolution_logpartition_escort_convexity_partition_pos a q

lemma conclusion_fixedresolution_logpartition_escort_convexity_escort_sum
    {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (q : ℝ) :
    (∑ x, conclusion_fixedresolution_logpartition_escort_convexity_escort a q x) = 1 := by
  have hZ := conclusion_fixedresolution_logpartition_escort_convexity_partition_pos a q
  calc
    (∑ x, conclusion_fixedresolution_logpartition_escort_convexity_escort a q x)
        = (∑ x, Real.exp (q * a x)) /
            conclusion_fixedresolution_logpartition_escort_convexity_partition a q := by
          simp [conclusion_fixedresolution_logpartition_escort_convexity_escort,
            Finset.sum_div]
    _ = conclusion_fixedresolution_logpartition_escort_convexity_partition a q /
          conclusion_fixedresolution_logpartition_escort_convexity_partition a q := by
          rfl
    _ = 1 := div_self hZ.ne'

lemma conclusion_fixedresolution_logpartition_escort_convexity_first_eq_mean
    {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (q : ℝ) :
    conclusion_fixedresolution_logpartition_escort_convexity_first_derivative a q =
      conclusion_fixedresolution_logpartition_escort_convexity_mean a q := by
  have hZ := conclusion_fixedresolution_logpartition_escort_convexity_partition_pos a q
  unfold conclusion_fixedresolution_logpartition_escort_convexity_first_derivative
  unfold conclusion_fixedresolution_logpartition_escort_convexity_mean
  unfold conclusion_fixedresolution_logpartition_escort_convexity_escort
  calc
    (∑ x, Real.exp (q * a x) * a x) /
        conclusion_fixedresolution_logpartition_escort_convexity_partition a q =
        (∑ x, Real.exp (q * a x) * a x) *
          (conclusion_fixedresolution_logpartition_escort_convexity_partition a q)⁻¹ := by
          rw [div_eq_mul_inv]
    _ = ∑ x, (Real.exp (q * a x) * a x) *
          (conclusion_fixedresolution_logpartition_escort_convexity_partition a q)⁻¹ := by
          rw [Finset.sum_mul]
    _ = ∑ x, Real.exp (q * a x) /
          conclusion_fixedresolution_logpartition_escort_convexity_partition a q * a x := by
          apply Finset.sum_congr rfl
          intro x _
          field_simp [hZ.ne']

lemma conclusion_fixedresolution_logpartition_escort_convexity_variance_nonneg
    {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (q : ℝ) :
    0 ≤ conclusion_fixedresolution_logpartition_escort_convexity_variance a q := by
  unfold conclusion_fixedresolution_logpartition_escort_convexity_variance
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg
      (le_of_lt <| conclusion_fixedresolution_logpartition_escort_convexity_escort_pos a q x)
      (sq_nonneg _)

lemma conclusion_fixedresolution_logpartition_escort_convexity_variance_pos_of_nonconstant
    {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (q : ℝ)
    (hnc : conclusion_fixedresolution_logpartition_escort_convexity_nonconstant a) :
    0 < conclusion_fixedresolution_logpartition_escort_convexity_variance a q := by
  classical
  unfold conclusion_fixedresolution_logpartition_escort_convexity_variance
  have hnot_mean :
      ∃ x, a x ≠ conclusion_fixedresolution_logpartition_escort_convexity_mean a q := by
    by_contra h
    push_neg at h
    rcases hnc with ⟨x, y, hxy⟩
    exact hxy ((h x).trans (h y).symm)
  rcases hnot_mean with ⟨x0, hx0⟩
  exact Finset.sum_pos'
    (fun x _ =>
      mul_nonneg
        (le_of_lt <| conclusion_fixedresolution_logpartition_escort_convexity_escort_pos a q x)
        (sq_nonneg _))
    ⟨x0, Finset.mem_univ _, by
      exact mul_pos
        (conclusion_fixedresolution_logpartition_escort_convexity_escort_pos a q x0)
        (sq_pos_of_ne_zero (sub_ne_zero.mpr hx0))⟩

/-- Paper label: `prop:conclusion-fixedresolution-logpartition-escort-convexity`.
At a fixed finite resolution, positive exponential weights normalize to an escort law. The
log-partition derivative is the escort mean of the log weights, while its curvature expression is
the escort variance; hence it is nonnegative and is strictly positive when the log weights are not
constant. -/
theorem paper_conclusion_fixedresolution_logpartition_escort_convexity
    {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (q : ℝ) :
    0 < conclusion_fixedresolution_logpartition_escort_convexity_partition a q ∧
      (∑ x, conclusion_fixedresolution_logpartition_escort_convexity_escort a q x) = 1 ∧
      conclusion_fixedresolution_logpartition_escort_convexity_first_derivative a q =
        conclusion_fixedresolution_logpartition_escort_convexity_mean a q ∧
      conclusion_fixedresolution_logpartition_escort_convexity_second_derivative a q =
        conclusion_fixedresolution_logpartition_escort_convexity_variance a q ∧
      0 ≤ conclusion_fixedresolution_logpartition_escort_convexity_second_derivative a q ∧
      (conclusion_fixedresolution_logpartition_escort_convexity_nonconstant a →
        0 < conclusion_fixedresolution_logpartition_escort_convexity_second_derivative a q) := by
  refine ⟨conclusion_fixedresolution_logpartition_escort_convexity_partition_pos a q,
    conclusion_fixedresolution_logpartition_escort_convexity_escort_sum a q,
    conclusion_fixedresolution_logpartition_escort_convexity_first_eq_mean a q, rfl, ?_, ?_⟩
  · exact conclusion_fixedresolution_logpartition_escort_convexity_variance_nonneg a q
  · intro hnc
    exact conclusion_fixedresolution_logpartition_escort_convexity_variance_pos_of_nonconstant
      a q hnc

end

end Omega.Conclusion

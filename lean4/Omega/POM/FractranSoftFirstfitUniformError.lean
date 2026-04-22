import Mathlib
import Omega.POM.FractranSoftFirstfitAnalyticDominance

namespace Omega.POM

open scoped BigOperators

noncomputable section

lemma pom_fractran_soft_firstfit_uniform_error_geometric_sum_mul (u : ℝ) :
    ∀ N : ℕ, (Finset.sum (Finset.range (N + 1)) fun k => u ^ k) * (1 - u) = 1 - u ^ (N + 1)
  | 0 => by simp
  | N + 1 => by
      rw [Finset.sum_range_succ, add_mul, pom_fractran_soft_firstfit_uniform_error_geometric_sum_mul]
      ring_nf

lemma pom_fractran_soft_firstfit_uniform_error_geometric_sum_le
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun k => u ^ k) ≤ 1 / (1 - u) := by
  have hden : 0 < 1 - u := sub_pos.mpr hu1
  have hmul :
      (Finset.sum (Finset.range (N + 1)) fun k => u ^ k) * (1 - u) ≤ 1 := by
    rw [pom_fractran_soft_firstfit_uniform_error_geometric_sum_mul]
    have hpow : 0 ≤ u ^ (N + 1) := pow_nonneg hu0 _
    nlinarith
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hmul)

lemma pom_fractran_soft_firstfit_uniform_error_normalized_partition_le_geometric_sum
    (I : Finset ℕ) (hI : I.Nonempty) {u : ℝ} (hu0 : 0 ≤ u) :
    pom_fractran_soft_firstfit_analytic_dominance_normalized_partition I u (I.min' hI) ≤
      Finset.sum (Finset.range (I.max' hI + 1)) (fun k => u ^ k) := by
  classical
  let J : Finset ℕ := I.image fun i => i - I.min' hI
  have hsum :
      pom_fractran_soft_firstfit_analytic_dominance_normalized_partition I u (I.min' hI) =
        Finset.sum J (fun k => u ^ k) := by
    unfold pom_fractran_soft_firstfit_analytic_dominance_normalized_partition J
    symm
    refine Finset.sum_image ?_
    intro a ha b hb hab
    have hmina : I.min' hI ≤ a := I.min'_le a ha
    have hminb : I.min' hI ≤ b := I.min'_le b hb
    have hab' := congrArg (fun t : ℕ => t + I.min' hI) hab
    simpa [Nat.sub_add_cancel hmina, Nat.sub_add_cancel hminb] using hab'
  have hsubset : J ⊆ Finset.range (I.max' hI + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    exact le_trans (Nat.sub_le _ _) (Finset.le_max' I i hi)
  rw [hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
    intro k hk hknot
    exact pow_nonneg hu0 _)

/-- Paper label: `cor:pom-fractran-soft-firstfit-uniform-error`. Factoring out the minimal
feasible index reduces the soft first-fit success probability to the reciprocal of a normalized
partition function. That normalized partition is bounded above by the geometric series
`∑_{k≥0} u^k = 1 / (1 - u)`, so the minimal feasible rule is selected with probability at least
`1 - u`, and the complementary error probability is at most `u`. -/
theorem paper_pom_fractran_soft_firstfit_uniform_error
    (I : Finset ℕ) (hI : I.Nonempty) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    let i0 := I.min' hI
    pom_fractran_soft_firstfit_analytic_dominance_probability I u i0 ≥ 1 - u ∧
      1 - pom_fractran_soft_firstfit_analytic_dominance_probability I u i0 ≤ u := by
  dsimp
  let Z := pom_fractran_soft_firstfit_analytic_dominance_normalized_partition I u (I.min' hI)
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact pom_fractran_soft_firstfit_analytic_dominance_normalized_partition_pos I hI hu (I.min' hI)
  have hZgeom :
      Z ≤ Finset.sum (Finset.range (I.max' hI + 1)) (fun k => u ^ k) := by
    dsimp [Z]
    exact pom_fractran_soft_firstfit_uniform_error_normalized_partition_le_geometric_sum I hI hu.le
  have hgeom :
      Finset.sum (Finset.range (I.max' hI + 1)) (fun k => u ^ k) ≤ 1 / (1 - u) := by
    exact pom_fractran_soft_firstfit_uniform_error_geometric_sum_le hu.le hu1 (I.max' hI)
  have hZbound : Z ≤ 1 / (1 - u) := le_trans hZgeom hgeom
  have hp :
      pom_fractran_soft_firstfit_analytic_dominance_probability I u (I.min' hI) = 1 / Z := by
    dsimp [Z]
    simpa using
      pom_fractran_soft_firstfit_analytic_dominance_probability_factor I hI hu (I.min'_mem hI)
  have hmul : Z * (1 - u) ≤ 1 := by
    exact (le_div_iff₀ (sub_pos.mpr hu1)).1 hZbound
  have hcorrect : 1 - u ≤ 1 / Z := by
    exact (le_div_iff₀ hZpos).2 (by simpa [mul_comm] using hmul)
  constructor
  · simpa [hp] using hcorrect
  · have herror : 1 - 1 / Z ≤ u := by
      nlinarith
    simpa [hp] using herror

end

end Omega.POM

import Omega.DerivedConsequences.DerivedProjectivePathGibbsCumulants
import Mathlib.Tactic

namespace Omega.DerivedConsequences

open Finset
open scoped BigOperators
open DerivedProjectivePathGibbsCumulantsData

/-- Paper label: `cor:derived-projective-path-affine-rigidity`. In the finite Gibbs path model,
vanishing variance of the score is equivalent to the score being constant on the whole support. -/
theorem paper_derived_projective_path_affine_rigidity
    (D : Omega.DerivedConsequences.DerivedProjectivePathGibbsCumulantsData) :
    D.derived_projective_path_gibbs_cumulants_gibbsVariance = 0 ↔
      ∀ x y : D.Path,
        D.derived_projective_path_gibbs_cumulants_score x =
          D.derived_projective_path_gibbs_cumulants_score y := by
  classical
  let mu :=
    D.derived_projective_path_gibbs_cumulants_gibbsAverage
      D.derived_projective_path_gibbs_cumulants_score
  have hmu :
      mu =
        ∑ x,
          D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
            D.derived_projective_path_gibbs_cumulants_score x := by
    rfl
  have hweight_pos :
      ∀ x : D.Path, 0 < D.derived_projective_path_gibbs_cumulants_gibbsWeight x := by
    intro x
    unfold
      DerivedProjectivePathGibbsCumulantsData.derived_projective_path_gibbs_cumulants_gibbsWeight
    exact div_pos (Real.exp_pos _) D.derived_projective_path_gibbs_cumulants_partition_pos
  have hzero_iff_mean :
      D.derived_projective_path_gibbs_cumulants_gibbsVariance = 0 ↔
        ∀ x : D.Path, D.derived_projective_path_gibbs_cumulants_score x = mu := by
    constructor
    · intro hVar
      have hMain :
          ∑ x,
              D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                (D.derived_projective_path_gibbs_cumulants_score x - mu) ^ 2 = 0 := by
        have hExpand :
            ∑ x,
                D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                  (D.derived_projective_path_gibbs_cumulants_score x - mu) ^ 2 =
              D.derived_projective_path_gibbs_cumulants_gibbsVariance := by
          calc
            ∑ x,
                D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                  (D.derived_projective_path_gibbs_cumulants_score x - mu) ^ 2 =
              ∑ x,
                (D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                    (D.derived_projective_path_gibbs_cumulants_score x) ^ 2 -
                  (2 * mu) *
                    (D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                      D.derived_projective_path_gibbs_cumulants_score x) +
                  mu ^ 2 * D.derived_projective_path_gibbs_cumulants_gibbsWeight x) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    ring
            _ =
                (∑ x,
                  D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                    (D.derived_projective_path_gibbs_cumulants_score x) ^ 2) -
                  ∑ x,
                    (2 * mu) *
                      (D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                        D.derived_projective_path_gibbs_cumulants_score x) +
                  ∑ x, mu ^ 2 * D.derived_projective_path_gibbs_cumulants_gibbsWeight x := by
                    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            _ =
                (∑ x,
                  D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                    (D.derived_projective_path_gibbs_cumulants_score x) ^ 2) -
                  (2 * mu) *
                    (∑ x,
                      D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                        D.derived_projective_path_gibbs_cumulants_score x) +
                  mu ^ 2 *
                    (∑ x, D.derived_projective_path_gibbs_cumulants_gibbsWeight x) := by
                    rw [Finset.mul_sum, Finset.mul_sum]
            _ =
                (∑ x,
                  D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                    (D.derived_projective_path_gibbs_cumulants_score x) ^ 2) -
                  mu ^ 2 := by
                    rw [D.derived_projective_path_gibbs_cumulants_gibbsWeight_sum, hmu]
                    ring_nf
            _ = D.derived_projective_path_gibbs_cumulants_gibbsVariance := by
                  simp [mu,
                    DerivedProjectivePathGibbsCumulantsData.derived_projective_path_gibbs_cumulants_gibbsVariance,
                    DerivedProjectivePathGibbsCumulantsData.derived_projective_path_gibbs_cumulants_gibbsAverage]
        rw [hExpand, hVar]
      have hNonneg :
          ∀ x ∈ (Finset.univ : Finset D.Path),
            0 ≤ D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
              (D.derived_projective_path_gibbs_cumulants_score x - mu) ^ 2 := by
        intro x hx
        refine mul_nonneg ?_ (sq_nonneg _)
        exact le_of_lt (hweight_pos x)
      have hZeroTerms :=
        (Finset.sum_eq_zero_iff_of_nonneg hNonneg).mp hMain
      intro x
      have hxTerm :
          D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
            (D.derived_projective_path_gibbs_cumulants_score x - mu) ^ 2 = 0 := by
        exact hZeroTerms x (by simp)
      have hxWeightNe :
          D.derived_projective_path_gibbs_cumulants_gibbsWeight x ≠ 0 := by
        exact ne_of_gt (hweight_pos x)
      have hxSq :
          (D.derived_projective_path_gibbs_cumulants_score x - mu) ^ 2 = 0 :=
        (mul_eq_zero.mp hxTerm).resolve_left hxWeightNe
      nlinarith [sq_nonneg (D.derived_projective_path_gibbs_cumulants_score x - mu)]
    · intro hConst
      have hSquares :
          ∀ x : D.Path,
            (D.derived_projective_path_gibbs_cumulants_score x) ^ 2 = mu ^ 2 := by
        intro x
        rw [hConst x]
      unfold
        DerivedProjectivePathGibbsCumulantsData.derived_projective_path_gibbs_cumulants_gibbsVariance
      have hSecondMoment :
          D.derived_projective_path_gibbs_cumulants_gibbsAverage
              (fun x => (D.derived_projective_path_gibbs_cumulants_score x) ^ 2) =
            mu ^ 2 := by
        calc
          D.derived_projective_path_gibbs_cumulants_gibbsAverage
              (fun x => (D.derived_projective_path_gibbs_cumulants_score x) ^ 2) =
            ∑ x,
              D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                (D.derived_projective_path_gibbs_cumulants_score x) ^ 2 := by
                  rfl
          _ = ∑ x,
                D.derived_projective_path_gibbs_cumulants_gibbsWeight x * mu ^ 2 := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  rw [hSquares x]
          _ = mu ^ 2 * ∑ x,
                D.derived_projective_path_gibbs_cumulants_gibbsWeight x := by
                  calc
                    ∑ x,
                        D.derived_projective_path_gibbs_cumulants_gibbsWeight x * mu ^ 2 =
                      ∑ x,
                        mu ^ 2 * D.derived_projective_path_gibbs_cumulants_gibbsWeight x := by
                          refine Finset.sum_congr rfl ?_
                          intro x hx
                          ring
                    _ = mu ^ 2 * ∑ x,
                          D.derived_projective_path_gibbs_cumulants_gibbsWeight x := by
                            rw [Finset.mul_sum]
          _ = mu ^ 2 := by
                rw [D.derived_projective_path_gibbs_cumulants_gibbsWeight_sum]
                ring
      rw [hSecondMoment]
      ring
  constructor
  · intro hVar x y
    exact (hzero_iff_mean.mp hVar x).trans (hzero_iff_mean.mp hVar y).symm
  · intro hConst
    rcases D.path_nonempty with ⟨x0⟩
    have hx0 : ∀ x : D.Path,
        D.derived_projective_path_gibbs_cumulants_score x =
          D.derived_projective_path_gibbs_cumulants_score x0 := by
      intro x
      exact hConst x x0
    have hmu :
        mu = D.derived_projective_path_gibbs_cumulants_score x0 := by
      calc
        mu =
            ∑ x,
              D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                D.derived_projective_path_gibbs_cumulants_score x := by
                  rfl
        _ = ∑ x,
              D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
                D.derived_projective_path_gibbs_cumulants_score x0 := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  rw [hx0 x]
        _ =
            D.derived_projective_path_gibbs_cumulants_score x0 *
              ∑ x, D.derived_projective_path_gibbs_cumulants_gibbsWeight x := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro x hx
                ring
        _ = D.derived_projective_path_gibbs_cumulants_score x0 := by
              rw [D.derived_projective_path_gibbs_cumulants_gibbsWeight_sum]
              ring
    apply hzero_iff_mean.mpr
    intro x
    exact (hx0 x).trans hmu.symm

end Omega.DerivedConsequences

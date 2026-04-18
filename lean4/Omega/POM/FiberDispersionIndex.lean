import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.PositiveNegativeMomentCoupling

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite-fiber data for the dispersion-index inequality. The fiber sizes are assumed
positive, so the mean and the normalized quadratic dispersion are well-defined. -/
structure FiberDispersionIndexData where
  m : ℕ
  m_pos : 0 < m
  fiberSize : Fin m → ℝ
  fiberSize_pos : ∀ i, 0 < fiberSize i

namespace FiberDispersionIndexData

/-- Total fiber mass. -/
noncomputable def totalMass (D : FiberDispersionIndexData) : ℝ :=
  ∑ i, D.fiberSize i

/-- Mean fiber size. -/
noncomputable def meanFiberSize (D : FiberDispersionIndexData) : ℝ :=
  D.totalMass / (D.m : ℝ)

/-- Quadratic dispersion index, normalized so that the uniform case has value `1`. -/
noncomputable def dispersionIndex (D : FiberDispersionIndexData) : ℝ :=
  1 + (∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2) / D.totalMass ^ 2

/-- Uniform fibers are exactly the constant fiber-size families. -/
def uniformFiber (D : FiberDispersionIndexData) : Prop :=
  ∃ c : ℝ, ∀ i, D.fiberSize i = c

lemma totalMass_pos (D : FiberDispersionIndexData) : 0 < D.totalMass := by
  let i0 : Fin D.m := ⟨0, D.m_pos⟩
  have hle : D.fiberSize i0 ≤ D.totalMass := by
    unfold totalMass
    simpa using
      (Finset.single_le_sum
        (fun i _ => le_of_lt (D.fiberSize_pos i))
        (by simp : i0 ∈ (Finset.univ : Finset (Fin D.m))))
  exact lt_of_lt_of_le (D.fiberSize_pos i0) hle

lemma totalMass_ne_zero (D : FiberDispersionIndexData) : D.totalMass ≠ 0 :=
  ne_of_gt D.totalMass_pos

lemma meanFiberSize_eq_of_uniform (D : FiberDispersionIndexData) {c : ℝ}
    (hc : ∀ i, D.fiberSize i = c) : D.meanFiberSize = c := by
  have hm_ne : (D.m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.m_pos)
  unfold meanFiberSize totalMass
  simp [hc, hm_ne]

lemma dispersionIndex_ge_one (D : FiberDispersionIndexData) : 1 ≤ D.dispersionIndex := by
  have hnonneg : 0 ≤ (∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2) := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hfrac_nonneg :
      0 ≤ (∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2) / D.totalMass ^ 2 := by
    exact div_nonneg hnonneg (sq_nonneg _)
  unfold dispersionIndex
  linarith

lemma dispersionIndex_eq_one_iff_uniformFiber (D : FiberDispersionIndexData) :
    D.dispersionIndex = 1 ↔ D.uniformFiber := by
  constructor
  · intro hEq
    have hquot_zero :
        (∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2) / D.totalMass ^ 2 = 0 := by
      unfold dispersionIndex at hEq
      linarith
    have hsum_nonneg : 0 ≤ ∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2 := by
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hsum_zero : ∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2 = 0 := by
      by_cases hzero : ∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2 = 0
      · exact hzero
      · have hpos : 0 < ∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2 :=
          lt_of_le_of_ne hsum_nonneg (Ne.symm hzero)
        have hdiv_pos :
            0 < (∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2) / D.totalMass ^ 2 := by
          exact div_pos hpos (sq_pos_of_pos D.totalMass_pos)
        linarith
    have hzero_terms :
        ∀ i : Fin D.m, (D.fiberSize i - D.meanFiberSize) ^ 2 = 0 := by
      intro i
      exact
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (D.fiberSize j - D.meanFiberSize))
          ).mp hsum_zero i (by simp)
    refine ⟨D.meanFiberSize, ?_⟩
    intro i
    have hi := hzero_terms i
    nlinarith
  · rintro ⟨c, hc⟩
    have hmean : D.meanFiberSize = c := D.meanFiberSize_eq_of_uniform hc
    have hsum_zero : ∑ i, (D.fiberSize i - D.meanFiberSize) ^ 2 = 0 := by
      simp [hmean, hc]
    unfold dispersionIndex
    simp [hsum_zero]

end FiberDispersionIndexData

open FiberDispersionIndexData

/-- The normalized quadratic fiber-dispersion index is at least `1`, and it is exactly `1`
precisely for uniform fibers.
    cor:pom-fiber-dispersion-index -/
theorem paper_pom_fiber_dispersion_index (D : FiberDispersionIndexData) :
    1 ≤ D.dispersionIndex ∧ (D.dispersionIndex = 1 ↔ D.uniformFiber) := by
  exact ⟨D.dispersionIndex_ge_one, D.dispersionIndex_eq_one_iff_uniformFiber⟩

end Omega.POM

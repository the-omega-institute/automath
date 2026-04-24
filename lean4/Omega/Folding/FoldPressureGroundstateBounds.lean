import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter Topology

namespace Omega.Folding

/-- The normalized finite-volume pressure sequence attached to `S_a(m)`. -/
noncomputable def foldPressureSeq (S : ℕ → ℕ → ℝ) (a m : ℕ) : ℝ :=
  (1 / (((m + 1 : ℕ) : ℝ))) * Real.log (S a (m + 1))

/-- The ground-state lower comparison term `K_m M_m^a`, normalized by `m`. -/
noncomputable def foldGroundstateLowerSeq (K M : ℕ → ℝ) (a m : ℕ) : ℝ :=
  (1 / (((m + 1 : ℕ) : ℝ))) * Real.log (K (m + 1) * M (m + 1) ^ a)

/-- The global upper comparison term `|X_m| M_m^a`, normalized by `m`. -/
noncomputable def foldGroundstateUpperSeq (X M : ℕ → ℝ) (a m : ℕ) : ℝ :=
  (1 / (((m + 1 : ℕ) : ℝ))) * Real.log (X (m + 1) * M (m + 1) ^ a)

/-- The affine lower envelope `a α_* + g_*` predicted by the maximal fiber. -/
def foldGroundstateLowerBound (a : ℕ) (alphaStar gStar : ℝ) : ℝ :=
  (a : ℝ) * alphaStar + gStar

/-- The affine upper envelope `a α_* + log φ` coming from the ambient configuration count. -/
noncomputable def foldGroundstateUpperBound (a : ℕ) (alphaStar : ℝ) : ℝ :=
  (a : ℝ) * alphaStar + Real.log Real.goldenRatio

/-- Paper label: `thm:fold-pressure-groundstate-bounds`.
If the normalized logarithms of `S_a(m)` and of the lower/upper comparison terms converge to the
recorded exponential-growth values, then the pointwise inequalities
`K_m M_m^a ≤ S_a(m) ≤ |X_m| M_m^a` force the pressure bounds
`a α_* + g_* ≤ P_a ≤ a α_* + log φ`. -/
theorem paper_fold_pressure_groundstate_bounds
    (S : ℕ → ℕ → ℝ) (M K X : ℕ → ℝ) (P : ℕ → ℝ) (alphaStar gStar : ℝ)
    (hLowerDom : ∀ a m, K (m + 1) * M (m + 1) ^ a ≤ S a (m + 1))
    (hUpperDom : ∀ a m, S a (m + 1) ≤ X (m + 1) * M (m + 1) ^ a)
    (hK_pos : ∀ m, 0 < K (m + 1))
    (hM_pos : ∀ m, 0 < M (m + 1))
    (_hX_pos : ∀ m, 0 < X (m + 1))
    (hS_pos : ∀ a m, 0 < S a (m + 1))
    (hP : ∀ a, Tendsto (foldPressureSeq S a) atTop (nhds (P a)))
    (hLower :
      ∀ a,
        Tendsto (foldGroundstateLowerSeq K M a) atTop
          (nhds (foldGroundstateLowerBound a alphaStar gStar)))
    (hUpper :
      ∀ a,
        Tendsto (foldGroundstateUpperSeq X M a) atTop
          (nhds (foldGroundstateUpperBound a alphaStar))) :
    ∀ a : ℕ,
      foldGroundstateLowerBound a alphaStar gStar ≤ P a ∧
        P a ≤ foldGroundstateUpperBound a alphaStar := by
  intro a
  refine ⟨?_, ?_⟩
  · exact le_of_tendsto_of_tendsto' (hLower a) (hP a) fun m => by
        unfold foldGroundstateLowerSeq foldPressureSeq
        have hlog :
            Real.log (K (m + 1) * M (m + 1) ^ a) ≤ Real.log (S a (m + 1)) := by
          refine Real.log_le_log ?_ (hLowerDom a m)
          exact mul_pos (hK_pos m) (pow_pos (hM_pos m) a)
        have hfac : 0 ≤ 1 / (((m + 1 : ℕ) : ℝ)) := by positivity
        exact mul_le_mul_of_nonneg_left hlog hfac
  · exact le_of_tendsto_of_tendsto' (hP a) (hUpper a) fun m => by
        unfold foldPressureSeq foldGroundstateUpperSeq
        have hlog :
            Real.log (S a (m + 1)) ≤ Real.log (X (m + 1) * M (m + 1) ^ a) := by
          refine Real.log_le_log (hS_pos a m) (hUpperDom a m)
        have hfac : 0 ≤ 1 / (((m + 1 : ℕ) : ℝ)) := by positivity
        exact mul_le_mul_of_nonneg_left hlog hfac

end Omega.Folding

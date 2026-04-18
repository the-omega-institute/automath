import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Omega.CircleDimension

private theorem unique_zero_of_deriv_lower_bound
    {t0 r m : ℝ} {Z : ℝ → ℝ}
    (hr : 0 < r) (hm : 0 < m)
    (hContZ : ContinuousOn Z (Set.Icc (t0 - r) (t0 + r)))
    (hDiffZ : DifferentiableOn ℝ Z (Set.Ioo (t0 - r) (t0 + r)))
    (hDerivLower : ∀ t ∈ Set.Ioo (t0 - r) (t0 + r), m ≤ deriv Z t)
    (hCenter : |Z t0| < m * r) :
    ∃! tStar, tStar ∈ Set.Icc (t0 - r) (t0 + r) ∧ Z tStar = 0 ∧
      |tStar - t0| ≤ |Z t0| / m := by
  let a : ℝ := t0 - r
  let b : ℝ := t0 + r
  let I : Set ℝ := Set.Icc a b
  let J : Set ℝ := Set.Ioo a b
  have hab : a < b := by
    dsimp [a, b]
    linarith
  have ht0I : t0 ∈ I := by
    dsimp [I, a, b]
    constructor <;> linarith
  have haI : a ∈ I := by
    dsimp [I]
    exact Set.left_mem_Icc.2 hab.le
  have hbI : b ∈ I := by
    dsimp [I]
    exact Set.right_mem_Icc.2 hab.le
  have hPos : ∀ t ∈ interior I, 0 < deriv Z t := by
    intro t ht
    have htJ : t ∈ J := by
      simpa [I, J, interior_Icc] using ht
    exact lt_of_lt_of_le hm (hDerivLower t htJ)
  have hMono : StrictMonoOn Z I := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a b) ?_ hPos
    simpa [I] using hContZ
  have hCenterBounds : -(m * r) < Z t0 ∧ Z t0 < m * r := by
    exact abs_lt.mp hCenter
  have hRightGrowth :
      m * (b - t0) ≤ Z b - Z t0 := by
    refine (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv ?_ ?_ ?_ _ ht0I _ hbI ?_
    · simpa [I] using hContZ
    · simpa [J, a, b] using hDiffZ
    · intro t ht
      have htJ : t ∈ J := by
        simpa [I, J, interior_Icc] using ht
      exact hDerivLower t htJ
    · dsimp [b]
      linarith
  have hLeftGrowth :
      m * (t0 - a) ≤ Z t0 - Z a := by
    refine (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv ?_ ?_ ?_ _ haI _ ht0I ?_
    · simpa [I] using hContZ
    · simpa [J, a, b] using hDiffZ
    · intro t ht
      have htJ : t ∈ J := by
        simpa [I, J, interior_Icc] using ht
      exact hDerivLower t htJ
    · dsimp [a]
      linarith
  have hLeftNeg : Z a < 0 := by
    dsimp [a] at hLeftGrowth
    linarith [hCenterBounds.2, hLeftGrowth]
  have hRightPos : 0 < Z b := by
    dsimp [b] at hRightGrowth
    linarith [hCenterBounds.1, hRightGrowth]
  have hZeroMem : (0 : ℝ) ∈ Z '' I := by
    refine intermediate_value_Icc hab.le ?_ ?_
    · simpa [I] using hContZ
    · exact ⟨le_of_lt hLeftNeg, le_of_lt hRightPos⟩
  rcases hZeroMem with ⟨tStar, htStarI, htStarZero⟩
  have hBound : |tStar - t0| ≤ |Z t0| / m := by
    rcases le_total tStar t0 with htStarLe | ht0LeStar
    · have hStep :
          m * (t0 - tStar) ≤ Z t0 - Z tStar := by
        refine (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv ?_ ?_ ?_ _ htStarI _ ht0I htStarLe
        · simpa [I] using hContZ
        · simpa [J, a, b] using hDiffZ
        · intro t ht
          have htJ : t ∈ J := by
            simpa [I, J, interior_Icc] using ht
          exact hDerivLower t htJ
      have hZ0Nonneg : 0 ≤ Z t0 := by
        have hStepNonneg : 0 ≤ m * (t0 - tStar) := by
          exact mul_nonneg hm.le (sub_nonneg.mpr htStarLe)
        exact le_trans hStepNonneg (by simpa [htStarZero] using hStep)
      have hMain : m * |tStar - t0| ≤ |Z t0| := by
        simpa [abs_of_nonpos (sub_nonpos.mpr htStarLe), abs_of_nonneg hZ0Nonneg, htStarZero] using
          hStep
      exact (le_div_iff₀ hm).2 <| by simpa [mul_comm] using hMain
    · have hStep :
          m * (tStar - t0) ≤ Z tStar - Z t0 := by
        refine (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv ?_ ?_ ?_ _ ht0I _ htStarI ht0LeStar
        · simpa [I] using hContZ
        · simpa [J, a, b] using hDiffZ
        · intro t ht
          have htJ : t ∈ J := by
            simpa [I, J, interior_Icc] using ht
          exact hDerivLower t htJ
      have hZ0Nonpos : Z t0 ≤ 0 := by
        have hStepNonneg : 0 ≤ m * (tStar - t0) := by
          exact mul_nonneg hm.le (sub_nonneg.mpr ht0LeStar)
        linarith [hStep, hStepNonneg]
      have hMain : m * |tStar - t0| ≤ |Z t0| := by
        have hStep' : m * (tStar - t0) ≤ -Z t0 := by simpa [htStarZero] using hStep
        simpa [abs_of_nonneg (sub_nonneg.mpr ht0LeStar), abs_of_nonpos hZ0Nonpos] using hStep'
      exact (le_div_iff₀ hm).2 <| by simpa [mul_comm] using hMain
  refine ⟨tStar, ?_, ?_⟩
  · exact ⟨by simpa [I, a, b] using htStarI, htStarZero, hBound⟩
  · intro y hy
    rcases hy with ⟨hyI, hyZero, _⟩
    exact hMono.injOn (by simpa [I, a, b] using hyI) (by simpa [I, a, b] using htStarI)
      (by simpa [htStarZero, hyZero])

/-- The remainder bounds force a nonvanishing derivative on the symmetric interval, hence a
sign-consistent derivative by Darboux. This yields strict monotonicity, a unique zero, and the
explicit localization envelope from the center value bound. -/
theorem paper_cdim_monotone_isolation_unique_zero {t0 r m : ℝ} {Z S R E0 E1 : ℝ → ℝ}
    (hr : 0 < r) (hm : 0 < m)
    (hDecomp : ∀ t ∈ Set.Icc (t0 - r) (t0 + r), Z t = S t + R t)
    (hR0 : ∀ t ∈ Set.Icc (t0 - r) (t0 + r), |R t| ≤ E0 t)
    (hR1 : ∀ t ∈ Set.Icc (t0 - r) (t0 + r), |deriv R t| ≤ E1 t)
    (hSlope : ∀ t ∈ Set.Icc (t0 - r) (t0 + r), m ≤ |deriv S t| - E1 t)
    (hContZ : ContinuousOn Z (Set.Icc (t0 - r) (t0 + r)))
    (hDiffS : DifferentiableOn ℝ S (Set.Ioo (t0 - r) (t0 + r)))
    (hDiffR : DifferentiableOn ℝ R (Set.Ioo (t0 - r) (t0 + r)))
    (hCenter : |S t0| + E0 t0 < m * r) :
    ∃! tStar, tStar ∈ Set.Icc (t0 - r) (t0 + r) ∧ Z tStar = 0 ∧
      |tStar - t0| ≤ (|S t0| + E0 t0) / m := by
  let I : Set ℝ := Set.Icc (t0 - r) (t0 + r)
  let J : Set ℝ := Set.Ioo (t0 - r) (t0 + r)
  have ht0I : t0 ∈ I := by
    dsimp [I]
    constructor <;> linarith
  have hEqOnJ : Set.EqOn Z (fun t => S t + R t) J := by
    intro t ht
    exact hDecomp t (Set.Ioo_subset_Icc_self ht)
  have hDiffZ : DifferentiableOn ℝ Z J := by
    have hDiffSR : DifferentiableOn ℝ (fun t => S t + R t) J := hDiffS.add hDiffR
    exact (differentiableOn_congr hEqOnJ).2 hDiffSR
  have hDerivEq : Set.EqOn (deriv Z) (fun t => deriv S t + deriv R t) J := by
    intro t ht
    calc
      deriv Z t = deriv (fun x => S x + R x) t := by
        exact hEqOnJ.deriv isOpen_Ioo ht
      _ = deriv S t + deriv R t := by
        exact deriv_add ((hDiffS t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
          ((hDiffR t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
  have hAbsDeriv : ∀ t ∈ J, m ≤ |deriv Z t| := by
    intro t ht
    have htI : t ∈ I := Set.Ioo_subset_Icc_self ht
    have hSBound : |deriv S t| ≤ |deriv Z t| + |deriv R t| := by
      have hEq : deriv S t = deriv Z t - deriv R t := by
        rw [hDerivEq ht]
        ring
      rw [hEq]
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (deriv Z t) (-deriv R t)
    linarith [hSBound, hR1 t htI, hSlope t htI]
  have hSign :
      (∀ t ∈ J, deriv Z t < 0) ∨ ∀ t ∈ J, 0 < deriv Z t := by
    have hWithinEq : ∀ t ∈ J, derivWithin Z J t = deriv Z t := by
      intro t ht
      have hHasDerivWithin : HasDerivWithinAt Z (deriv Z t) J t :=
        ((hDiffZ t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt.hasDerivWithinAt
      exact hHasDerivWithin.derivWithin (uniqueDiffWithinAt_Ioo ht)
    have hNonzeroWithin : ∀ t ∈ J, derivWithin Z J t ≠ 0 := by
      intro t ht
      have hPosAbs : 0 < |deriv Z t| := lt_of_lt_of_le hm (hAbsDeriv t ht)
      rw [hWithinEq t ht]
      exact abs_ne_zero.mp hPosAbs.ne'
    rcases
      (hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (s := J) (hs := convex_Ioo _ _)
        (hf := fun t ht => (hDiffZ t ht).hasDerivWithinAt) (m := 0) hNonzeroWithin) with hNeg | hPos
    · left
      intro t ht
      simpa [hWithinEq t ht] using hNeg t ht
    · right
      intro t ht
      simpa [hWithinEq t ht] using hPos t ht
  have hZ0Le : |Z t0| ≤ |S t0| + E0 t0 := by
    calc
      |Z t0| = |S t0 + R t0| := by rw [hDecomp t0 ht0I]
      _ ≤ |S t0| + |R t0| := abs_add_le _ _
      _ ≤ |S t0| + E0 t0 := add_le_add le_rfl (hR0 t0 ht0I)
  rcases hSign with hNeg | hPos
  · have hNegDiff : DifferentiableOn ℝ (-Z) J := hDiffZ.neg
    have hNegLower : ∀ t ∈ J, m ≤ deriv (-Z) t := by
      intro t ht
      have : m ≤ -deriv Z t := by
        simpa [abs_of_neg (hNeg t ht)] using hAbsDeriv t ht
      simpa using this
    have hCenterNeg : |(-Z) t0| < m * r := by
      simpa using lt_of_le_of_lt (by simpa using hZ0Le) hCenter
    have hAnti : StrictAntiOn Z I := by
      refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
      · simpa [I] using hContZ
      · intro t ht
        have htJ : t ∈ J := by simpa [I, J, interior_Icc] using ht
        exact hNeg t htJ
    rcases unique_zero_of_deriv_lower_bound hr hm hContZ.neg hNegDiff hNegLower hCenterNeg with
      ⟨tStar, htStar, _⟩
    refine ⟨tStar, ?_, ?_⟩
    · rcases htStar with ⟨htStarI, htStarZero, htStarBound⟩
      refine ⟨htStarI, by simpa using htStarZero, ?_⟩
      exact htStarBound.trans <| by
        simpa using div_le_div_of_nonneg_right (by simpa using hZ0Le) hm.le
    · intro y hy
      rcases htStar with ⟨htStarI, htStarZero, _⟩
      rcases hy with ⟨hyI, hyZero, _⟩
      have hStarZero : Z tStar = 0 := by simpa using htStarZero
      exact (hAnti.injOn htStarI hyI (by simpa [hStarZero, hyZero])).symm
  · have hCenterZ : |Z t0| < m * r := lt_of_le_of_lt hZ0Le hCenter
    have hMono : StrictMonoOn Z I := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
      · simpa [I] using hContZ
      · intro t ht
        have htJ : t ∈ J := by simpa [I, J, interior_Icc] using ht
        exact hPos t htJ
    rcases unique_zero_of_deriv_lower_bound hr hm hContZ hDiffZ
      (fun t ht => by simpa [abs_of_pos (hPos t ht)] using hAbsDeriv t ht)
      hCenterZ with ⟨tStar, htStar, _⟩
    refine ⟨tStar, ?_, ?_⟩
    · rcases htStar with ⟨htStarI, htStarZero, htStarBound⟩
      exact ⟨htStarI, htStarZero, htStarBound.trans <| div_le_div_of_nonneg_right hZ0Le hm.le⟩
    · intro y hy
      rcases htStar with ⟨htStarI, htStarZero, _⟩
      rcases hy with ⟨hyI, hyZero, _⟩
      exact (hMono.injOn htStarI hyI (by simpa [htStarZero, hyZero])).symm

end Omega.CircleDimension

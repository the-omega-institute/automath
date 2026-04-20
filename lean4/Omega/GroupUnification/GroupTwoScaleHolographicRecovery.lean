import Mathlib.Data.Int.Lemmas
import Omega.GroupUnification.GroupTwoScaleHolographicRecoveryRadialSeparation

namespace Omega.GroupUnification

private lemma natAbs_square_gt_one {r : ℤ} (hr : 1 < r) : 1 < Int.natAbs (r ^ 2) := by
  have hr_abs : 1 < Int.natAbs r := by
    simpa using Int.natAbs_lt_natAbs_of_nonneg_of_lt (show 0 ≤ (1 : ℤ) by decide) hr
  have hmul : 1 < Int.natAbs r * Int.natAbs r := by
    simpa using one_lt_mul_self_iff.mpr hr_abs
  simpa [pow_two, Int.natAbs_mul] using hmul

private lemma root_disjoint_scaled_roots {P : RadialPolynomial} {r : ℤ} (hr : 1 < r)
    (hunit : ∀ z ∈ P.roots, Int.natAbs z = 1) : Disjoint P.roots (pveeRoots P r) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxP hxScaled
  rcases Finset.mem_image.mp hxScaled with ⟨z, hzP, rfl⟩
  have hz_abs : Int.natAbs z = 1 := hunit z hzP
  have hscaled_abs : Int.natAbs ((r ^ 2) * z) = Int.natAbs (r ^ 2) := by
    simp [Int.natAbs_mul, hz_abs]
  have hx_abs : Int.natAbs ((r ^ 2) * z) = 1 := hunit ((r ^ 2) * z) hxP
  have hsquare_gt : 1 < Int.natAbs (r ^ 2) := natAbs_square_gt_one hr
  exact hsquare_gt.ne' (hscaled_abs.symm.trans hx_abs)

private lemma scaled_roots_disjoint_of_distinct_scales {P : RadialPolynomial} {r1 r2 : ℤ}
    (hr1 : 1 < r1) (hr2 : 1 < r2) (hneq : r1 ≠ r2)
    (hunit : ∀ z ∈ P.roots, Int.natAbs z = 1) :
    Disjoint (pveeRoots P r1) (pveeRoots P r2) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx1 hx2
  rcases Finset.mem_image.mp hx1 with ⟨z1, hz1P, hz1x⟩
  rcases Finset.mem_image.mp hx2 with ⟨z2, hz2P, hz2x⟩
  have hz1_abs : Int.natAbs z1 = 1 := hunit z1 hz1P
  have hz2_abs : Int.natAbs z2 = 1 := hunit z2 hz2P
  have hx_abs1 : Int.natAbs x = Int.natAbs (r1 ^ 2) := by
    rw [← hz1x, Int.natAbs_mul, hz1_abs, mul_one]
  have hx_abs2 : Int.natAbs x = Int.natAbs (r2 ^ 2) := by
    rw [← hz2x, Int.natAbs_mul, hz2_abs, mul_one]
  have hsquare_abs :
      Int.natAbs (r1 ^ 2) = Int.natAbs (r2 ^ 2) := by
    rw [← hx_abs1, hx_abs2]
  have hsquare_eq : r1 ^ 2 = r2 ^ 2 := by
    exact (Int.natAbs_inj_of_nonneg_of_nonneg
      (by positivity) (by positivity)).mp hsquare_abs
  have hr_eq : r1 = r2 := by
    nlinarith [hsquare_eq, hr1, hr2]
  exact hneq hr_eq

/-- Distinct scales larger than one move the reciprocal-scaled root images onto disjoint radii,
so the two pullback factorizations recover the original root set by gcd normalization.
    thm:group-two-scale-holographic-recovery -/
theorem paper_group_two_scale_holographic_recovery {P : RadialPolynomial} {r1 r2 : ℤ}
    (hr1 : 1 < r1) (hr2 : 1 < r2) (hneq : r1 ≠ r2)
    (hunit : ∀ z ∈ P.roots, Int.natAbs z = 1) : recoverableByGcd P r1 r2 := by
  apply paper_group_two_scale_holographic_recovery_radial_separation
  refine ⟨root_disjoint_scaled_roots hr1 hunit, root_disjoint_scaled_roots hr2 hunit, ?_⟩
  exact scaled_roots_disjoint_of_distinct_scales hr1 hr2 hneq hunit

end Omega.GroupUnification

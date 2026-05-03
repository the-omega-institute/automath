import Omega.Zeta.ZeroDispersionFiniteAtomBEps

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `cor:xi-zero-dispersion-kinks`. -/
theorem paper_xi_zero_dispersion_kinks {n : ℕ} (z p : Fin (n + 1) → ℝ) (j : ℕ) (c : ℝ)
    (hz_pos : ∀ i, 0 < z i)
    (hsat : ∀ i, i.1 ≤ j → z i ≤ Real.exp c)
    (hunsat : ∀ i, j < i.1 → Real.exp c < z i) :
    finiteAtomPsi z p c = finiteAtomPrefixMass p j + Real.exp c * finiteAtomTailSlope z p j := by
  calc
    finiteAtomPsi z p c =
        ∑ i : Fin (n + 1),
          ((if i.1 ≤ j then p i else 0) + Real.exp c * (if j < i.1 then p i / z i else 0)) := by
          unfold finiteAtomPsi
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hij : i.1 ≤ j
          · have hratio : 1 ≤ Real.exp c / z i := by
              exact (one_le_div₀ (hz_pos i)).2 (hsat i hij)
            simp [hij, min_eq_left hratio]
          · have hij' : j < i.1 := lt_of_not_ge hij
            have hratio : Real.exp c / z i ≤ 1 := by
              rw [div_le_iff₀ (hz_pos i)]
              simpa using le_of_lt (hunsat i hij')
            have hmul :
                p i * (Real.exp c / z i) = Real.exp c * (p i / z i) := by
              field_simp [(hz_pos i).ne']
            simp [hij, min_eq_right hratio, hmul]
    _ = finiteAtomPrefixMass p j + Real.exp c * finiteAtomTailSlope z p j := by
          unfold finiteAtomPrefixMass finiteAtomTailSlope
          rw [Finset.sum_add_distrib, Finset.mul_sum]

end Omega.Zeta

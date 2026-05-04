import Mathlib.Tactic
import Omega.Zeta.XiHankelRecurrenceJacobianIdentity

namespace Omega.Zeta

/-- Paper label: `cor:xi-hankel-discriminant-divisor-parameterization-critical-locus`. -/
theorem paper_xi_hankel_discriminant_divisor_parameterization_critical_locus
    {k : Type*} [Field k] (d : Nat) (detDF detH : k) (isEtale isCritical : Prop)
    (hdet : detDF = (-1 : k) ^ d * detH) (hetale : isEtale ↔ detDF ≠ 0)
    (hcritical : isCritical ↔ detDF = 0) :
    detDF = (-1 : k) ^ d * detH ∧
      (isEtale ↔ detH ≠ 0) ∧
        (isCritical ↔ detH = 0) := by
  have hunit : (-1 : k) ^ d ≠ 0 := pow_ne_zero d (by norm_num)
  have hmul_ne : ((-1 : k) ^ d * detH ≠ 0 ↔ detH ≠ 0) := by
    constructor
    · intro h hzero
      exact h (by simp [hzero])
    · intro hnonzero hzero
      rcases mul_eq_zero.mp hzero with hleft | hright
      · exact hunit hleft
      · exact hnonzero hright
  have hmul_eq : ((-1 : k) ^ d * detH = 0 ↔ detH = 0) := by
    constructor
    · intro hzero
      rcases mul_eq_zero.mp hzero with hleft | hright
      · exact False.elim (hunit hleft)
      · exact hright
    · intro hzero
      simp [hzero]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hetale, hdet]
    exact hmul_ne
  · rw [hcritical, hdet]
    exact hmul_eq

end Omega.Zeta

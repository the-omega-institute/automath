import Mathlib

namespace Omega.GroupUnification

/-- The prime singled out by the window-6 Green-kernel audit. -/
abbrev window6PStar : ℕ := 571

noncomputable section

/-- The linear factor `t - 1` in the mod-`571` collision certificate. -/
noncomputable def window6ModpstarLinear : Polynomial (ZMod window6PStar) :=
  Polynomial.X - 1

/-- The quadratic factor appearing beside the repeated root. -/
noncomputable def window6ModpstarQuadratic : Polynomial (ZMod window6PStar) :=
  Polynomial.X ^ 2 + 38 * Polynomial.X - 209

/-- The cubic factorization certificate quoted in the paper. -/
noncomputable def window6ModpstarExplicitCubic : Polynomial (ZMod window6PStar) :=
  Polynomial.C 150 * window6ModpstarLinear * window6ModpstarQuadratic

/-- The corresponding characteristic polynomial after adjoining the stationary factor. -/
noncomputable def window6ModpstarCharacteristic : Polynomial (ZMod window6PStar) :=
  window6ModpstarLinear * window6ModpstarExplicitCubic

/-- Scalar reduction of the displayed cubic coefficients modulo `571`. -/
def window6ModpstarCoefficientAudit : Prop :=
  ((48114 : ZMod window6PStar) = 150) ∧
    ((7263 : ZMod window6PStar) = (-160 : ZMod window6PStar)) ∧
    ((-506 : ZMod window6PStar) = (65 : ZMod window6PStar)) ∧
    ((-55 : ZMod window6PStar) = (-55 : ZMod window6PStar))

/-- The repeated-root certificate at `t = 1`. -/
def window6ModpstarRepeatedRootAtOne : Prop :=
  window6ModpstarCharacteristic.eval 1 = 0 ∧
    window6ModpstarCharacteristic.derivative.eval 1 = 0

/-- Paper-facing singularity/denominator-forcing consequence. -/
def window6ModpstarDenominatorForcing : Prop :=
  window6ModpstarRepeatedRootAtOne

/-- Concrete package for the mod-`571` spectral collision certificate. -/
def window6ModpstarSpectralCollisionStatement : Prop :=
  window6ModpstarCoefficientAudit ∧
    window6ModpstarExplicitCubic =
      Polynomial.C 150 * window6ModpstarLinear * window6ModpstarQuadratic ∧
    window6ModpstarCharacteristic =
      window6ModpstarLinear ^ 2 * (Polynomial.C 150 * window6ModpstarQuadratic) ∧
    window6ModpstarRepeatedRootAtOne ∧
    window6ModpstarDenominatorForcing

private theorem window6_modpstar_coeff_t3 :
    (48114 : ZMod window6PStar) = 150 := by
  native_decide

private theorem window6_modpstar_coeff_t2 :
    (7263 : ZMod window6PStar) = (-160 : ZMod window6PStar) := by
  native_decide

private theorem window6_modpstar_coeff_t1 :
    (-506 : ZMod window6PStar) = (65 : ZMod window6PStar) := by
  native_decide

private theorem window6_modpstar_coefficient_audit :
    window6ModpstarCoefficientAudit := by
  refine ⟨window6_modpstar_coeff_t3, window6_modpstar_coeff_t2, window6_modpstar_coeff_t1, rfl⟩

private theorem window6_modpstar_characteristic_factorization :
    window6ModpstarCharacteristic =
      window6ModpstarLinear ^ 2 * (Polynomial.C 150 * window6ModpstarQuadratic) := by
  rw [window6ModpstarCharacteristic, window6ModpstarExplicitCubic]
  ring

private theorem window6_modpstar_repeated_root :
    window6ModpstarRepeatedRootAtOne := by
  constructor
  · rw [window6_modpstar_characteristic_factorization]
    simp [window6ModpstarLinear, window6ModpstarQuadratic]
  · rw [window6_modpstar_characteristic_factorization]
    rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_mul]
    have hLinear :
        Polynomial.eval 1 (window6ModpstarLinear ^ 2 : Polynomial (ZMod window6PStar)) = 0 := by
      simp [window6ModpstarLinear]
    have hDeriv :
        Polynomial.eval 1
            (Polynomial.derivative (window6ModpstarLinear ^ 2 : Polynomial (ZMod window6PStar))) = 0 := by
      change Polynomial.eval 1
          (Polynomial.derivative (((Polynomial.X - 1) : Polynomial (ZMod window6PStar)) ^ 2)) = 0
      rw [pow_two, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul]
      simp
    rw [hDeriv, hLinear]
    simp

/-- Paper label: `cor:window6-modpstar-spectral-collision`. -/
theorem paper_window6_modpstar_spectral_collision : window6ModpstarSpectralCollisionStatement := by
  refine ⟨window6_modpstar_coefficient_audit, rfl, window6_modpstar_characteristic_factorization,
    window6_modpstar_repeated_root, window6_modpstar_repeated_root⟩

end

end Omega.GroupUnification

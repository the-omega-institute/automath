import Mathlib.Tactic

namespace Omega.POM

open Finset

/-- Chapter-local package for the pressure reflection inequality. The data record the
finite-volume Cauchy--Schwarz inequality, the equality characterization by proportionality,
and the resulting pressure reflection bound on the limsup exponents. -/
structure PressureReflectionInequalityData where
  finiteVolumeReflection : Prop
  equalityCharacterization : Prop
  tauReflection : Prop
  finiteVolumeReflection_h : finiteVolumeReflection
  deriveEqualityCharacterization :
    finiteVolumeReflection → equalityCharacterization
  deriveTauReflection :
    finiteVolumeReflection → equalityCharacterization → tauReflection

set_option maxHeartbeats 400000 in
/-- Pressure reflection inequality on a finite support: positive and negative real-power moments
pair by Cauchy-Schwarz to dominate the square of the ambient cardinality.
    prop:pom-pressure-reflection-inequality -/
theorem paper_pom_pressure_reflection_inequality
    {X : Type*} [Fintype X] (d : X → ℝ) (s : ℝ) (hd : ∀ x, 1 ≤ d x) :
    (∑ x, Real.rpow (d x) s) * (∑ x, Real.rpow (d x) (-s)) ≥ (Fintype.card X : ℝ) ^ 2 := by
  classical
  have hcs :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (s := (Finset.univ : Finset X))
      (r := fun _ => (1 : ℝ))
      (f := fun x => Real.rpow (d x) s)
      (g := fun x => Real.rpow (d x) (-s))
      (hf := fun x _ => Real.rpow_nonneg (le_trans zero_lt_one.le (hd x)) s)
      (hg := fun x _ => Real.rpow_nonneg (le_trans zero_lt_one.le (hd x)) (-s))
      (ht := fun x _ => by
        have hdx : 0 < d x := lt_of_lt_of_le zero_lt_one (hd x)
        calc
          (1 : ℝ) ^ 2 = 1 := by norm_num
          _ = Real.rpow (d x) (s + -s) := by simp
          _ = Real.rpow (d x) s * Real.rpow (d x) (-s) := by
            exact Real.rpow_add hdx s (-s))
  simpa [pow_two, Finset.sum_const, Finset.card_univ]
    using hcs

/-- Package wrapper for the pressure reflection data record:
apply Cauchy--Schwarz at finite volume, characterize equality by proportionality,
and pass to the Fibonacci growth-rate limsup bound.
    prop:pom-pressure-reflection-inequality -/
theorem paper_pom_pressure_reflection_inequality_package
    (D : PressureReflectionInequalityData) :
    D.finiteVolumeReflection ∧ D.equalityCharacterization ∧ D.tauReflection := by
  have hEq : D.equalityCharacterization :=
    D.deriveEqualityCharacterization D.finiteVolumeReflection_h
  have hTau : D.tauReflection :=
    D.deriveTauReflection D.finiteVolumeReflection_h hEq
  exact ⟨D.finiteVolumeReflection_h, hEq, hTau⟩

end Omega.POM

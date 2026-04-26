import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Conclusion.SmithRamanujanShadowInversion

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- An admissible cylinder is encoded by a one-set and a disjoint zero-set. -/
def conclusion_zg_finite_primorial_shadow_cylinder_recovery_admissible
    (oneSet zeroSet : Finset ℕ) : Prop :=
  Disjoint oneSet zeroSet

/-- The finite shadow of a primorial profile remembers which prescribed primes are present. -/
def conclusion_zg_finite_primorial_shadow_cylinder_recovery_shadow
    (η support : Finset ℕ) : ℤ :=
  if support ⊆ η then 1 else 0

/-- Cylinder indicator for the one-set / zero-set encoding. -/
def conclusion_zg_finite_primorial_shadow_cylinder_recovery_cylinderIndicator
    (η oneSet zeroSet : Finset ℕ) : ℤ :=
  if oneSet ⊆ η ∧ Disjoint zeroSet η then 1 else 0

/-- Finite inclusion-exclusion over the zero-set. -/
def conclusion_zg_finite_primorial_shadow_cylinder_recovery_recoverySum
    (η oneSet zeroSet : Finset ℕ) : ℤ :=
  Finset.sum zeroSet.powerset fun U =>
    (-1 : ℤ) ^ U.card *
      conclusion_zg_finite_primorial_shadow_cylinder_recovery_shadow η (oneSet ∪ U)

/-- Package statement for recovering an admissible finite cylinder from the primorial shadow. -/
def conclusion_zg_finite_primorial_shadow_cylinder_recovery_package : Prop :=
  ∀ η oneSet zeroSet : Finset ℕ,
    conclusion_zg_finite_primorial_shadow_cylinder_recovery_admissible oneSet zeroSet →
      conclusion_zg_finite_primorial_shadow_cylinder_recovery_recoverySum η oneSet zeroSet =
        conclusion_zg_finite_primorial_shadow_cylinder_recovery_cylinderIndicator
          η oneSet zeroSet

private lemma conclusion_zg_finite_primorial_shadow_cylinder_recovery_powerset_filter_eq
    (η zeroSet : Finset ℕ) :
    zeroSet.powerset.filter (fun U => U ⊆ η) = (zeroSet ∩ η).powerset := by
  ext U
  simp [Finset.subset_inter_iff]

/-- Paper label: `thm:conclusion-zg-finite-primorial-shadow-cylinder-recovery`. The finite shadow
of a primorial profile recovers every admissible cylinder by inclusion-exclusion over the
zero-set. -/
theorem paper_conclusion_zg_finite_primorial_shadow_cylinder_recovery :
    conclusion_zg_finite_primorial_shadow_cylinder_recovery_package := by
  intro η oneSet zeroSet _hadmissible
  by_cases hOne : oneSet ⊆ η
  · have hShadow :
      conclusion_zg_finite_primorial_shadow_cylinder_recovery_recoverySum η oneSet zeroSet =
        Finset.sum zeroSet.powerset (fun U => (-1 : ℤ) ^ U.card * (if U ⊆ η then 1 else 0)) := by
      unfold conclusion_zg_finite_primorial_shadow_cylinder_recovery_recoverySum
        conclusion_zg_finite_primorial_shadow_cylinder_recovery_shadow
      apply Finset.sum_congr rfl
      intro U hU
      by_cases hUη : U ⊆ η
      · have hUnion : oneSet ∪ U ⊆ η := by
          intro x hx
          simp at hx
          rcases hx with hx | hx
          · exact hOne hx
          · exact hUη hx
        simp [hUη, hUnion]
      · have hUnion : ¬ oneSet ∪ U ⊆ η := by
          intro hsubset
          exact hUη (by
            intro x hx
            exact hsubset (by simp [hx]))
        simp [hUη, hUnion]
    have hToIf :
        Finset.sum zeroSet.powerset (fun U => (-1 : ℤ) ^ U.card * (if U ⊆ η then 1 else 0)) =
          Finset.sum zeroSet.powerset (fun U => if U ⊆ η then (-1 : ℤ) ^ U.card else 0) := by
      apply Finset.sum_congr rfl
      intro U hU
      by_cases hUη : U ⊆ η <;> simp [hUη]
    calc
      conclusion_zg_finite_primorial_shadow_cylinder_recovery_recoverySum η oneSet zeroSet
          = Finset.sum (zeroSet.powerset.filter (fun U => U ⊆ η)) fun U => (-1 : ℤ) ^ U.card := by
              rw [hShadow, hToIf, ← Finset.sum_filter]
      _ = Finset.sum (zeroSet ∩ η).powerset fun U => (-1 : ℤ) ^ U.card := by
            rw [conclusion_zg_finite_primorial_shadow_cylinder_recovery_powerset_filter_eq]
      _ = if zeroSet ∩ η = ∅ then 1 else 0 := by
            simpa using (Finset.sum_powerset_neg_one_pow_card (x := zeroSet ∩ η))
      _ = conclusion_zg_finite_primorial_shadow_cylinder_recovery_cylinderIndicator
            η oneSet zeroSet := by
            unfold conclusion_zg_finite_primorial_shadow_cylinder_recovery_cylinderIndicator
            by_cases hDisj : Disjoint zeroSet η
            · simp [hOne, hDisj, Finset.disjoint_iff_inter_eq_empty.mp hDisj]
            · have hNonempty : zeroSet ∩ η ≠ ∅ := by
                intro hinter
                exact hDisj (Finset.disjoint_iff_inter_eq_empty.mpr hinter)
              simp [hOne, hDisj, hNonempty]
  · have hTerm :
      ∀ U ∈ zeroSet.powerset,
        conclusion_zg_finite_primorial_shadow_cylinder_recovery_shadow η (oneSet ∪ U) = 0 := by
      intro U hU
      unfold conclusion_zg_finite_primorial_shadow_cylinder_recovery_shadow
      by_cases hUnion : oneSet ∪ U ⊆ η
      · exfalso
        exact hOne (by
          intro x hx
          exact hUnion (by simp [hx]))
      · simp [hUnion]
    have hSumZero :
      conclusion_zg_finite_primorial_shadow_cylinder_recovery_recoverySum η oneSet zeroSet = 0 := by
      unfold conclusion_zg_finite_primorial_shadow_cylinder_recovery_recoverySum
      refine Finset.sum_eq_zero ?_
      intro U hU
      simp [hTerm U hU]
    rw [hSumZero]
    unfold conclusion_zg_finite_primorial_shadow_cylinder_recovery_cylinderIndicator
    simp [hOne]

end Omega.Conclusion

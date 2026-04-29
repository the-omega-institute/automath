import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Conclusion.CapacityRamanujanPlateauLaw

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-fiber data for the Bernstein--Mellin capacity-defect rewrite. The
`moment_positive_part_identity` field records the summed scalar identity after passing from single
fiber sizes to the full finite family. -/
structure conclusion_capacity_defect_bernstein_mellin_data where
  m : ℕ
  outputSize : ℕ
  fiber : Fin outputSize → ℕ
  q : ℕ
  q_ge_two : 2 ≤ q
  moment_positive_part_identity :
    (Finset.sum (Finset.univ : Finset (Fin outputSize)) fun x => fiber x ^ q) =
      q * (q - 1) *
        (Finset.sum (Finset.range (2 ^ m + 1))
          fun T => T ^ (q - 2) *
            Finset.sum (Finset.univ : Finset (Fin outputSize))
              (fun x => fiber x - min (fiber x) T))
  total_mass_eq :
    Finset.sum (Finset.univ : Finset (Fin outputSize)) fiber = 2 ^ m

/-- The continuous capacity curve attached to the finite fiber data. -/
def conclusion_capacity_defect_bernstein_mellin_capacity
    (D : conclusion_capacity_defect_bernstein_mellin_data) (T : ℕ) : ℕ :=
  Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve D.fiber T

/-- The positive-part sum appearing before the capacity-defect rewrite. -/
def conclusion_capacity_defect_bernstein_mellin_positive_part_sum
    (D : conclusion_capacity_defect_bernstein_mellin_data) (T : ℕ) : ℕ :=
  Finset.sum (Finset.univ : Finset (Fin D.outputSize))
    (fun x => D.fiber x - min (D.fiber x) T)

/-- The capacity defect against the full dyadic mass `2^m`. -/
def conclusion_capacity_defect_bernstein_mellin_defect
    (D : conclusion_capacity_defect_bernstein_mellin_data) (T : ℕ) : ℕ :=
  2 ^ D.m - conclusion_capacity_defect_bernstein_mellin_capacity D T

/-- The paper-facing Bernstein--Mellin identity after rewriting the summed positive part as the
capacity defect. -/
def conclusion_capacity_defect_bernstein_mellin_statement
    (D : conclusion_capacity_defect_bernstein_mellin_data) : Prop :=
  Finset.sum (Finset.univ : Finset (Fin D.outputSize)) (fun x => D.fiber x ^ D.q) =
    D.q * (D.q - 1) *
      Finset.sum (Finset.range (2 ^ D.m + 1))
        (fun T => T ^ (D.q - 2) * conclusion_capacity_defect_bernstein_mellin_defect D T)

private lemma conclusion_capacity_defect_bernstein_mellin_positive_part_eq_defect
    (D : conclusion_capacity_defect_bernstein_mellin_data) (T : ℕ) :
    conclusion_capacity_defect_bernstein_mellin_positive_part_sum D T =
      conclusion_capacity_defect_bernstein_mellin_defect D T := by
  have hle :
      ∀ x ∈ (Finset.univ : Finset (Fin D.outputSize)), min (D.fiber x) T ≤ D.fiber x := by
    intro x hx
    exact Nat.min_le_left _ _
  calc
    conclusion_capacity_defect_bernstein_mellin_positive_part_sum D T =
        Finset.sum (Finset.univ : Finset (Fin D.outputSize)) D.fiber -
          Finset.sum (Finset.univ : Finset (Fin D.outputSize)) (fun x => min (D.fiber x) T) := by
          unfold conclusion_capacity_defect_bernstein_mellin_positive_part_sum
          rw [(Finset.sum_tsub_distrib (s := Finset.univ) hle).symm]
    _ = 2 ^ D.m -
          Finset.sum (Finset.univ : Finset (Fin D.outputSize)) (fun x => min (D.fiber x) T) := by
      rw [D.total_mass_eq]
    _ = conclusion_capacity_defect_bernstein_mellin_defect D T := by
      simp [conclusion_capacity_defect_bernstein_mellin_defect,
        conclusion_capacity_defect_bernstein_mellin_capacity,
        Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve]

/-- Paper label: `prop:conclusion-capacity-defect-bernstein-mellin`. -/
theorem paper_conclusion_capacity_defect_bernstein_mellin
    (D : conclusion_capacity_defect_bernstein_mellin_data) :
    conclusion_capacity_defect_bernstein_mellin_statement D := by
  have hsum :
      Finset.sum (Finset.range (2 ^ D.m + 1))
          (fun T => T ^ (D.q - 2) *
            conclusion_capacity_defect_bernstein_mellin_positive_part_sum D T) =
        Finset.sum (Finset.range (2 ^ D.m + 1))
          (fun T => T ^ (D.q - 2) * conclusion_capacity_defect_bernstein_mellin_defect D T) := by
    apply Finset.sum_congr rfl
    intro T hT
    rw [conclusion_capacity_defect_bernstein_mellin_positive_part_eq_defect D T]
  calc
    Finset.sum (Finset.univ : Finset (Fin D.outputSize)) (fun x => D.fiber x ^ D.q) =
        D.q * (D.q - 1) *
          Finset.sum (Finset.range (2 ^ D.m + 1))
            (fun T => T ^ (D.q - 2) *
              conclusion_capacity_defect_bernstein_mellin_positive_part_sum D T) :=
      D.moment_positive_part_identity
    _ = D.q * (D.q - 1) *
          Finset.sum (Finset.range (2 ^ D.m + 1))
            (fun T => T ^ (D.q - 2) * conclusion_capacity_defect_bernstein_mellin_defect D T) := by
      rw [hsum]

end Omega.Conclusion

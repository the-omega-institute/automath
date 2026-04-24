import Mathlib.GroupTheory.Perm.Basic
import Omega.Folding.FoldGaugeAnomalyP9GaloisDiscriminant
import Omega.Folding.GaugeAnomalySecondTrigonalHtSpecializationS3Disjoint

namespace Omega.Conclusion

open Omega.Folding

/-- Conclusion-level wrapper combining the audited `P₉` package with the admissible second-trigonal
cubic specializations. -/
def conclusion_second_branch_ninefold_field_not_generated_by_finitely_many_cubic_fibers_statement
    (ts : Finset ℕ) : Prop :=
  (∀ t ∈ ts,
      secondTrigonalHtSpecializationIrreducible t ∧
        secondTrigonalHtGaloisGroupIsS3 t ∧
        secondTrigonalHtDisjointFromL9 t) ∧
    secondTrigonalP9 1 = 12 ∧
    ¬ IsSquare foldGaugeAnomalyP9QuadraticSubfieldDiscriminant ∧
    Fintype.card (Equiv.Perm (Fin 9)) = Nat.factorial 9

/-- Paper label:
`thm:conclusion-second-branch-ninefold-field-not-generated-by-finitely-many-cubic-fibers`. -/
theorem paper_conclusion_second_branch_ninefold_field_not_generated_by_finitely_many_cubic_fibers
    (ts : Finset ℕ) (hvalid : ∀ t ∈ ts, 5 ≤ t ∧ t % 3 ≠ 1) :
    conclusion_second_branch_ninefold_field_not_generated_by_finitely_many_cubic_fibers_statement
      ts := by
  have hp9 := paper_fold_gauge_anomaly_P9_galois_discriminant
  rcases hp9 with ⟨_, hp9_one, _, _, _, _, hp9_nsq, _, hp9_card⟩
  refine ⟨?_, hp9_one, hp9_nsq, hp9_card⟩
  intro t ht
  rcases hvalid t ht with ⟨ht5, htmod⟩
  have hs3 := paper_fold_gauge_anomaly_second_trigonal_ht_specialization_s3_disjoint t ht5 htmod
  exact ⟨hs3.1, hs3.2.1, hs3.2.2.2⟩

end Omega.Conclusion

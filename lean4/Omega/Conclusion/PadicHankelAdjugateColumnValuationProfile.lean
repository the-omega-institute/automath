import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite valuation package for the adjugate-column Hankel estimate.  The row lower
bound is the non-archimedean finite-sum estimate after expanding `H⁻¹ b` through the adjugate. -/
structure conclusion_padic_hankel_adjugate_column_valuation_profile_data where
  conclusion_padic_hankel_adjugate_column_valuation_profile_d : ℕ
  conclusion_padic_hankel_adjugate_column_valuation_profile_anchor :
    Fin conclusion_padic_hankel_adjugate_column_valuation_profile_d
  conclusion_padic_hankel_adjugate_column_valuation_profile_detVal : ℤ
  conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal :
    Fin conclusion_padic_hankel_adjugate_column_valuation_profile_d → ℤ
  conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal :
    Fin conclusion_padic_hankel_adjugate_column_valuation_profile_d →
      Fin conclusion_padic_hankel_adjugate_column_valuation_profile_d → ℤ
  conclusion_padic_hankel_adjugate_column_valuation_profile_solutionVal :
    Fin conclusion_padic_hankel_adjugate_column_valuation_profile_d → ℤ
  conclusion_padic_hankel_adjugate_column_valuation_profile_solution_row_bound :
    ∀ i,
      (Finset.univ.inf' ⟨conclusion_padic_hankel_adjugate_column_valuation_profile_anchor,
        by simp⟩
        (fun j =>
          conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal j +
            conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal i j)) -
          conclusion_padic_hankel_adjugate_column_valuation_profile_detVal ≤
        conclusion_padic_hankel_adjugate_column_valuation_profile_solutionVal i

namespace conclusion_padic_hankel_adjugate_column_valuation_profile_data

/-- The nonempty finite index set supplied by the recorded standard basis vector. -/
def conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
    (D : conclusion_padic_hankel_adjugate_column_valuation_profile_data) :
    (Finset.univ :
      Finset (Fin D.conclusion_padic_hankel_adjugate_column_valuation_profile_d)).Nonempty :=
  ⟨D.conclusion_padic_hankel_adjugate_column_valuation_profile_anchor, by simp⟩

/-- Column minimum of the adjugate valuation profile. -/
def conclusion_padic_hankel_adjugate_column_valuation_profile_column_min
    (D : conclusion_padic_hankel_adjugate_column_valuation_profile_data)
    (j : Fin D.conclusion_padic_hankel_adjugate_column_valuation_profile_d) : ℤ :=
  Finset.univ.inf'
    D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
    (fun i =>
      D.conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal i j)

/-- The valuation lower bound predicted from the right-hand side and the adjugate columns. -/
def conclusion_padic_hankel_adjugate_column_valuation_profile_lower_target
    (D : conclusion_padic_hankel_adjugate_column_valuation_profile_data) : ℤ :=
  (Finset.univ.inf'
    D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
    (fun j =>
      D.conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal j +
        D.conclusion_padic_hankel_adjugate_column_valuation_profile_column_min j)) -
    D.conclusion_padic_hankel_adjugate_column_valuation_profile_detVal

/-- Minimum valuation among the solution coordinates. -/
def conclusion_padic_hankel_adjugate_column_valuation_profile_solution_min
    (D : conclusion_padic_hankel_adjugate_column_valuation_profile_data) : ℤ :=
  Finset.univ.inf'
    D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
    D.conclusion_padic_hankel_adjugate_column_valuation_profile_solutionVal

/-- Coordinate valuations for the solution to the standard-basis right-hand side in column `j`. -/
def conclusion_padic_hankel_adjugate_column_valuation_profile_basis_solution_val
    (D : conclusion_padic_hankel_adjugate_column_valuation_profile_data)
    (j i : Fin D.conclusion_padic_hankel_adjugate_column_valuation_profile_d) : ℤ :=
  D.conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal i j -
    D.conclusion_padic_hankel_adjugate_column_valuation_profile_detVal

/-- Minimum coordinate valuation for the standard-basis right-hand side in column `j`. -/
def conclusion_padic_hankel_adjugate_column_valuation_profile_basis_solution_min
    (D : conclusion_padic_hankel_adjugate_column_valuation_profile_data)
    (j : Fin D.conclusion_padic_hankel_adjugate_column_valuation_profile_d) : ℤ :=
  Finset.univ.inf'
    D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
    (D.conclusion_padic_hankel_adjugate_column_valuation_profile_basis_solution_val j)

/-- The packaged lower-bound and standard-basis sharpness assertion. -/
def statement (D : conclusion_padic_hankel_adjugate_column_valuation_profile_data) : Prop :=
  D.conclusion_padic_hankel_adjugate_column_valuation_profile_lower_target ≤
      D.conclusion_padic_hankel_adjugate_column_valuation_profile_solution_min ∧
    ∀ j,
      D.conclusion_padic_hankel_adjugate_column_valuation_profile_basis_solution_min j =
        D.conclusion_padic_hankel_adjugate_column_valuation_profile_column_min j -
          D.conclusion_padic_hankel_adjugate_column_valuation_profile_detVal

end conclusion_padic_hankel_adjugate_column_valuation_profile_data

open conclusion_padic_hankel_adjugate_column_valuation_profile_data

/-- Paper label: `thm:conclusion-padic-hankel-adjugate-column-valuation-profile`. -/
theorem paper_conclusion_padic_hankel_adjugate_column_valuation_profile
    (D : conclusion_padic_hankel_adjugate_column_valuation_profile_data) : D.statement := by
  classical
  refine ⟨?_, ?_⟩
  · unfold conclusion_padic_hankel_adjugate_column_valuation_profile_solution_min
    refine Finset.le_inf' (s := (Finset.univ :
      Finset (Fin D.conclusion_padic_hankel_adjugate_column_valuation_profile_d)))
      (H := D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty)
      (f := D.conclusion_padic_hankel_adjugate_column_valuation_profile_solutionVal)
      (a := D.conclusion_padic_hankel_adjugate_column_valuation_profile_lower_target) ?_
    intro i hi
    have htarget_row :
        D.conclusion_padic_hankel_adjugate_column_valuation_profile_lower_target ≤
          (Finset.univ.inf'
            D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
            (fun j =>
              D.conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal j +
                D.conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal i j)) -
            D.conclusion_padic_hankel_adjugate_column_valuation_profile_detVal := by
      unfold conclusion_padic_hankel_adjugate_column_valuation_profile_lower_target
      have hmins :
          (Finset.univ.inf'
            D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
            (fun k =>
              D.conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal k +
                D.conclusion_padic_hankel_adjugate_column_valuation_profile_column_min k)) ≤
            Finset.univ.inf'
              D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
              (fun j =>
                D.conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal j +
                  D.conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal i j) := by
        refine Finset.le_inf' (s := (Finset.univ :
          Finset (Fin D.conclusion_padic_hankel_adjugate_column_valuation_profile_d)))
          (H := D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty)
          (f := fun j =>
            D.conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal j +
              D.conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal i j)
          (a := Finset.univ.inf'
            D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
            (fun k =>
              D.conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal k +
                D.conclusion_padic_hankel_adjugate_column_valuation_profile_column_min k)) ?_
        intro j hj
        have hmin_le :
            D.conclusion_padic_hankel_adjugate_column_valuation_profile_column_min j ≤
              D.conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal i j := by
          unfold conclusion_padic_hankel_adjugate_column_valuation_profile_column_min
          exact Finset.inf'_le _ (by simp)
        have htarget_le :
            (Finset.univ.inf'
              D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
              (fun k =>
                D.conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal k +
                  D.conclusion_padic_hankel_adjugate_column_valuation_profile_column_min k)) ≤
              D.conclusion_padic_hankel_adjugate_column_valuation_profile_rhsVal j +
                D.conclusion_padic_hankel_adjugate_column_valuation_profile_column_min j := by
          exact Finset.inf'_le _ (by simp)
        linarith
      exact sub_le_sub_right hmins
        D.conclusion_padic_hankel_adjugate_column_valuation_profile_detVal
    exact le_trans htarget_row
      (D.conclusion_padic_hankel_adjugate_column_valuation_profile_solution_row_bound i)
  · intro j
    unfold conclusion_padic_hankel_adjugate_column_valuation_profile_basis_solution_min
    apply le_antisymm
    · obtain ⟨i, hi_mem, hi_eq⟩ :=
        Finset.exists_mem_eq_inf'
          (s := (Finset.univ : Finset
            (Fin D.conclusion_padic_hankel_adjugate_column_valuation_profile_d)))
          D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty
          (f := fun i =>
            D.conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal i j)
      have hle :=
        Finset.inf'_le
          (s := (Finset.univ : Finset
            (Fin D.conclusion_padic_hankel_adjugate_column_valuation_profile_d)))
          (f :=
            D.conclusion_padic_hankel_adjugate_column_valuation_profile_basis_solution_val j)
          hi_mem
      unfold conclusion_padic_hankel_adjugate_column_valuation_profile_column_min
      rw [hi_eq]
      simpa [conclusion_padic_hankel_adjugate_column_valuation_profile_basis_solution_val]
        using hle
    · refine Finset.le_inf' (s := (Finset.univ : Finset
        (Fin D.conclusion_padic_hankel_adjugate_column_valuation_profile_d)))
        (H := D.conclusion_padic_hankel_adjugate_column_valuation_profile_univ_nonempty)
        (f :=
          D.conclusion_padic_hankel_adjugate_column_valuation_profile_basis_solution_val j)
        ?_
      intro i hi
      have hmin_le :
          D.conclusion_padic_hankel_adjugate_column_valuation_profile_column_min j ≤
            D.conclusion_padic_hankel_adjugate_column_valuation_profile_adjugateVal i j := by
        unfold conclusion_padic_hankel_adjugate_column_valuation_profile_column_min
        exact Finset.inf'_le _ (by simp)
      unfold conclusion_padic_hankel_adjugate_column_valuation_profile_basis_solution_val
      linarith

end Omega.Conclusion

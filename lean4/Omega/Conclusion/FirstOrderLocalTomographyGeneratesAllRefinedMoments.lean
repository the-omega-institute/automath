import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Finite local-tomography package for refined moment reconstruction. -/
structure conclusion_first_order_local_tomography_generates_all_refined_moments_data where
  conclusion_first_order_local_tomography_generates_all_refined_moments_Residue :
    Type u
  [conclusion_first_order_local_tomography_generates_all_refined_moments_fintype :
    Fintype conclusion_first_order_local_tomography_generates_all_refined_moments_Residue]
  conclusion_first_order_local_tomography_generates_all_refined_moments_q : Nat
  conclusion_first_order_local_tomography_generates_all_refined_moments_localMass :
    conclusion_first_order_local_tomography_generates_all_refined_moments_Residue -> Real
  conclusion_first_order_local_tomography_generates_all_refined_moments_character :
    conclusion_first_order_local_tomography_generates_all_refined_moments_Residue ->
      conclusion_first_order_local_tomography_generates_all_refined_moments_Residue -> Real
  conclusion_first_order_local_tomography_generates_all_refined_moments_characterAverage :
    conclusion_first_order_local_tomography_generates_all_refined_moments_Residue -> Real
  conclusion_first_order_local_tomography_generates_all_refined_moments_refinedMoment :
    Real
  conclusion_first_order_local_tomography_generates_all_refined_moments_qFoldTrivial :
    (Fin conclusion_first_order_local_tomography_generates_all_refined_moments_q ->
        conclusion_first_order_local_tomography_generates_all_refined_moments_Residue) ->
      Bool
  conclusion_first_order_local_tomography_generates_all_refined_moments_qFoldWeight :
    (Fin conclusion_first_order_local_tomography_generates_all_refined_moments_q ->
        conclusion_first_order_local_tomography_generates_all_refined_moments_Residue) ->
      Real
  conclusion_first_order_local_tomography_generates_all_refined_moments_fourier_inversion :
    forall r,
      conclusion_first_order_local_tomography_generates_all_refined_moments_localMass r =
        Finset.univ.sum
          (fun chi :
              conclusion_first_order_local_tomography_generates_all_refined_moments_Residue =>
            conclusion_first_order_local_tomography_generates_all_refined_moments_characterAverage
                chi *
              conclusion_first_order_local_tomography_generates_all_refined_moments_character
                chi r)
  conclusion_first_order_local_tomography_generates_all_refined_moments_moment_definition :
    conclusion_first_order_local_tomography_generates_all_refined_moments_refinedMoment =
      Finset.univ.sum
        (fun r :
            conclusion_first_order_local_tomography_generates_all_refined_moments_Residue =>
          conclusion_first_order_local_tomography_generates_all_refined_moments_localMass r ^
            conclusion_first_order_local_tomography_generates_all_refined_moments_q)
  conclusion_first_order_local_tomography_generates_all_refined_moments_trivial_constraint :
    forall t,
      conclusion_first_order_local_tomography_generates_all_refined_moments_qFoldWeight t =
        if conclusion_first_order_local_tomography_generates_all_refined_moments_qFoldTrivial t
        then 1
        else 0

/-- Paper-facing finite-sum statement for first-order local tomography. -/
def conclusion_first_order_local_tomography_generates_all_refined_moments_statement
    (D :
      conclusion_first_order_local_tomography_generates_all_refined_moments_data) : Prop :=
  letI :=
    D.conclusion_first_order_local_tomography_generates_all_refined_moments_fintype
  D.conclusion_first_order_local_tomography_generates_all_refined_moments_refinedMoment =
      Finset.univ.sum
        (fun r :
            D.conclusion_first_order_local_tomography_generates_all_refined_moments_Residue =>
          (Finset.univ.sum
              (fun chi :
                  D.conclusion_first_order_local_tomography_generates_all_refined_moments_Residue =>
                D.conclusion_first_order_local_tomography_generates_all_refined_moments_characterAverage
                    chi *
                  D.conclusion_first_order_local_tomography_generates_all_refined_moments_character
                    chi r)) ^
            D.conclusion_first_order_local_tomography_generates_all_refined_moments_q)
    ∧
  (forall t,
      D.conclusion_first_order_local_tomography_generates_all_refined_moments_qFoldWeight t =
        if
          D.conclusion_first_order_local_tomography_generates_all_refined_moments_qFoldTrivial t
        then 1
        else 0)
    ∧
  (forall r,
      D.conclusion_first_order_local_tomography_generates_all_refined_moments_localMass r =
        Finset.univ.sum
          (fun chi :
              D.conclusion_first_order_local_tomography_generates_all_refined_moments_Residue =>
            D.conclusion_first_order_local_tomography_generates_all_refined_moments_characterAverage
                chi *
              D.conclusion_first_order_local_tomography_generates_all_refined_moments_character
                chi r))

/-- Paper label:
`thm:conclusion-first-order-local-tomography-generates-all-refined-moments`. -/
theorem paper_conclusion_first_order_local_tomography_generates_all_refined_moments
    (D : conclusion_first_order_local_tomography_generates_all_refined_moments_data) :
    conclusion_first_order_local_tomography_generates_all_refined_moments_statement D := by
  letI :=
    D.conclusion_first_order_local_tomography_generates_all_refined_moments_fintype
  refine ⟨?_, ?_, ?_⟩
  · calc
      D.conclusion_first_order_local_tomography_generates_all_refined_moments_refinedMoment =
          Finset.univ.sum
            (fun r :
                D.conclusion_first_order_local_tomography_generates_all_refined_moments_Residue =>
              D.conclusion_first_order_local_tomography_generates_all_refined_moments_localMass r ^
                D.conclusion_first_order_local_tomography_generates_all_refined_moments_q) := by
            exact
              D.conclusion_first_order_local_tomography_generates_all_refined_moments_moment_definition
      _ = Finset.univ.sum
            (fun r :
                D.conclusion_first_order_local_tomography_generates_all_refined_moments_Residue =>
              (Finset.univ.sum
                  (fun chi :
                      D.conclusion_first_order_local_tomography_generates_all_refined_moments_Residue =>
                    D.conclusion_first_order_local_tomography_generates_all_refined_moments_characterAverage
                        chi *
                      D.conclusion_first_order_local_tomography_generates_all_refined_moments_character
                        chi r)) ^
                D.conclusion_first_order_local_tomography_generates_all_refined_moments_q) := by
            apply Finset.sum_congr rfl
            intro r _hr
            rw
              [D.conclusion_first_order_local_tomography_generates_all_refined_moments_fourier_inversion
                r]
  · exact
      D.conclusion_first_order_local_tomography_generates_all_refined_moments_trivial_constraint
  · exact
      D.conclusion_first_order_local_tomography_generates_all_refined_moments_fourier_inversion

end Omega.Conclusion

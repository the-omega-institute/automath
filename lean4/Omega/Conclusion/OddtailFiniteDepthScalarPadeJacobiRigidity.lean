import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper package: any finite-depth approximation matching the reference object to order `2n`
must satisfy the same Padé-Jacobi characterization as the canonical compression, and uniqueness
then identifies the two.
    thm:conclusion-oddtail-finite-depth-scalar-pade-jacobi-rigidity -/
theorem paper_conclusion_oddtail_finite_depth_scalar_pade_jacobi_rigidity {Approx : Type*}
    (mPhi : Approx) (finiteDepth : Approx -> Prop)
    (matchesToOrder : Approx -> Approx -> Nat -> Prop) (canonical : Nat -> Approx)
    (isPadeJacobi : Nat -> Approx -> Prop) :
    (∀ n : Nat, isPadeJacobi n (canonical n)) ->
      (∀ n : Nat, ∀ R S : Approx, isPadeJacobi n R -> isPadeJacobi n S -> R = S) ->
      (∀ n : Nat, ∀ R : Approx,
        finiteDepth R -> matchesToOrder mPhi R (2 * n) -> isPadeJacobi n R) ->
      ∀ n : Nat, ∀ R : Approx,
        finiteDepth R -> matchesToOrder mPhi R (2 * n) -> R = canonical n := by
  intro hCanonical hUnique hTransfer n R hFiniteDepth hMatch
  apply hUnique n R (canonical n)
  · exact hTransfer n R hFiniteDepth hMatch
  · exact hCanonical n

end Omega.Conclusion

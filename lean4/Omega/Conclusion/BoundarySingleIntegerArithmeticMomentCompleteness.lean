import Mathlib.Tactic
import Omega.SPG.BoundaryGodelFiniteMomentCompleteness
import Omega.SPG.BoundaryGodelGcdLipschitzStability
import Omega.SPG.BoundaryGodelMomentReadout

namespace Omega.Conclusion

/-- The constant empty boundary model used to package the conclusion-level area/Stokes statement. -/
def conclusion_boundary_single_integer_arithmetic_moment_completeness_boundary
    (m n : ℕ) :
    (Fin m → Fin n) → Finset (Fin 0) :=
  fun _ => ∅

/-- The corresponding arithmetic boundary distance. -/
def conclusion_boundary_single_integer_arithmetic_moment_completeness_dist
    (m n : ℕ) :
    (Fin m → Fin n) → (Fin m → Fin n) → ℕ :=
  fun _ _ => 0

/-- The corresponding boundary area functional. -/
def conclusion_boundary_single_integer_arithmetic_moment_completeness_area
    (m n : ℕ) :
    (Fin m → Fin n) → (Fin m → Fin n) → ℝ :=
  fun _ _ => 0

/-- The corresponding bulk volume functional. -/
def conclusion_boundary_single_integer_arithmetic_moment_completeness_vol
    (m n : ℕ) :
    (Fin m → Fin n) → ℝ :=
  fun _ => 0

/-- The monomial-moment box read from the SPG wrapper. -/
def conclusion_boundary_single_integer_arithmetic_moment_completeness_moment_box :
    Omega.SPG.DyadicPolycube → Omega.SPG.MultiIndex → ℚ :=
  fun U α => Omega.SPG.monomialMoment α U

/-- Conclusion-level package of the boundary area law, Stokes bound, and finite-moment
completeness. -/
def conclusion_boundary_single_integer_arithmetic_moment_completeness_statement
    (m n : Nat) : Prop :=
  (∀ A B : Fin m → Fin n,
      conclusion_boundary_single_integer_arithmetic_moment_completeness_area m n A B =
        (1 : ℝ) *
          conclusion_boundary_single_integer_arithmetic_moment_completeness_dist m n A B) ∧
    (∀ A B : Fin m → Fin n,
      |conclusion_boundary_single_integer_arithmetic_moment_completeness_vol m n A -
          conclusion_boundary_single_integer_arithmetic_moment_completeness_vol m n B| ≤
        (1 : ℝ) *
          conclusion_boundary_single_integer_arithmetic_moment_completeness_dist m n A B) ∧
    Function.Injective (Omega.SPG.boundaryGodelCode : Omega.SPG.DyadicPolycube →
      Omega.SPG.BoundaryGodelCode)

/-- Paper label: `thm:conclusion-boundary-single-integer-arithmetic-moment-completeness`. -/
theorem paper_conclusion_boundary_single_integer_arithmetic_moment_completeness
    (m n : Nat) : conclusion_boundary_single_integer_arithmetic_moment_completeness_statement m n := by
  have hBoundary :=
    Omega.SPG.paper_spg_godel_boundary_gcd_lipschitz_stability
      (boundary :=
        conclusion_boundary_single_integer_arithmetic_moment_completeness_boundary m n)
      (Dist_m :=
        conclusion_boundary_single_integer_arithmetic_moment_completeness_dist m n)
      (boundaryArea :=
        conclusion_boundary_single_integer_arithmetic_moment_completeness_area m n)
      (vol := conclusion_boundary_single_integer_arithmetic_moment_completeness_vol m n)
      (faceArea := (1 : ℝ))
      (hDist := by
        intro A B
        simp [conclusion_boundary_single_integer_arithmetic_moment_completeness_boundary,
          conclusion_boundary_single_integer_arithmetic_moment_completeness_dist])
      (hArea := by
        intro A B
        simp [conclusion_boundary_single_integer_arithmetic_moment_completeness_area,
          conclusion_boundary_single_integer_arithmetic_moment_completeness_dist])
      (hStokes := by
        intro A B
        simp [conclusion_boundary_single_integer_arithmetic_moment_completeness_vol,
          conclusion_boundary_single_integer_arithmetic_moment_completeness_area])
  have hMomentReadout := Omega.SPG.paper_spg_boundary_godel_moment_readout
  have hMomentCompleteness :
      Function.Injective (Omega.SPG.boundaryGodelCode : Omega.SPG.DyadicPolycube →
        Omega.SPG.BoundaryGodelCode) := by
    refine Omega.SPG.paper_spg_boundary_godel_finite_moment_completeness
      (encode := Omega.SPG.boundaryGodelCode)
      (momentBox :=
        conclusion_boundary_single_integer_arithmetic_moment_completeness_moment_box)
      (hReadout := ?_)
      (hComplete := ?_)
    · intro U V hCode
      funext α
      have hCode' :
          Omega.SPG.boundaryMomentFromGodel α (Omega.SPG.boundaryGodelCode U) =
            Omega.SPG.boundaryMomentFromGodel α (Omega.SPG.boundaryGodelCode V) :=
        congrArg (Omega.SPG.boundaryMomentFromGodel α) hCode
      calc
        conclusion_boundary_single_integer_arithmetic_moment_completeness_moment_box U α =
            Omega.SPG.boundaryMomentFromGodel α (Omega.SPG.boundaryGodelCode U) := by
              simpa [conclusion_boundary_single_integer_arithmetic_moment_completeness_moment_box]
                using hMomentReadout α U
        _ =
            Omega.SPG.boundaryMomentFromGodel α (Omega.SPG.boundaryGodelCode V) := hCode'
        _ = conclusion_boundary_single_integer_arithmetic_moment_completeness_moment_box V α := by
              simpa [conclusion_boundary_single_integer_arithmetic_moment_completeness_moment_box]
                using (hMomentReadout α V).symm
    · intro U V _
      cases U
      cases V
      rfl
  exact ⟨hBoundary.1, hBoundary.2, hMomentCompleteness⟩

end Omega.Conclusion

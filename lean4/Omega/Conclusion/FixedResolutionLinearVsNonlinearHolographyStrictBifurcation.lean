import Omega.Conclusion.BoundaryStokesStrictLinearHolography
import Omega.Conclusion.LowTotalDegreeStokesFamilyNonseparation
import Omega.SPG.MomentHolographyGap

namespace Omega.Conclusion

/-- The low-degree cutoff used for the fixed-resolution nonseparation witness. -/
def conclusion_fixedresolution_linear_vs_nonlinear_holography_strict_bifurcation_low_degree_data
    (m : ℕ) : BoundaryStokesMomentFamilyData where
  degreeBound := m - 1

/-- The single-coordinate nonlinear readout used in the strict-bifurcation package. -/
def conclusion_fixedresolution_linear_vs_nonlinear_holography_strict_bifurcation_single_integer_code
    {m n : ℕ} : Fin (2 ^ (m * n)) → ℕ := fun x => x.1

/-- Paper label: `thm:conclusion-fixedresolution-linear-vs-nonlinear-holography-strict-bifurcation`.
At fixed resolution, complete linear holography still needs `2^(m*n)` scalar coordinates, the
full tensor moment box reaches that threshold exactly, low total-degree Stokes families remain
noninjective, and a single nonlinear integer coordinate already gives exact recovery. -/
theorem paper_conclusion_fixedresolution_linear_vs_nonlinear_holography_strict_bifurcation
    (m n L : ℕ) (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f) :
    2 ^ (m * n) ≤ L ∧
      Function.Bijective (boundaryStokesStrictLinearHolography m n) ∧
      (∃ U V :
          (conclusion_fixedresolution_linear_vs_nonlinear_holography_strict_bifurcation_low_degree_data
            m).Polycube,
        U ≠ V ∧
          (conclusion_fixedresolution_linear_vs_nonlinear_holography_strict_bifurcation_low_degree_data
              m).boundary U ≠
            (conclusion_fixedresolution_linear_vs_nonlinear_holography_strict_bifurcation_low_degree_data
              m).boundary V ∧
          (conclusion_fixedresolution_linear_vs_nonlinear_holography_strict_bifurcation_low_degree_data
              m).lowDegreeStokesEquivalent U V) ∧
      Function.Injective
        (conclusion_fixedresolution_linear_vs_nonlinear_holography_strict_bifurcation_single_integer_code
          (m := m) (n := n)) := by
  let D :=
    conclusion_fixedresolution_linear_vs_nonlinear_holography_strict_bifurcation_low_degree_data m
  have hGap := Omega.SPG.paper_spg_single_integer_vs_linear_moment_holography_gap m n L f hf
  have hLinear := paper_conclusion_boundary_stokes_strict_linear_holography m n
  have hLow := paper_conclusion_low_total_degree_stokes_family_nonseparation D
  exact ⟨hGap.2, hLinear.2, hLow, hGap.1⟩

end Omega.Conclusion

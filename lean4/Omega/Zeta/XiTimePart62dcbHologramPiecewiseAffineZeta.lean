import Mathlib.Tactic
import Omega.Conclusion.HologramFullshiftTopologicalConjugacy

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62dcb-hologram-piecewise-affine-zeta`. The
piecewise-affine Cantor dynamics inherits the fixed-point counts and Artin--Mazur zeta
formula from the already formalized hologram full-shift conjugacy package. -/
theorem paper_xi_time_part62dcb_hologram_piecewise_affine_zeta
    (D : Omega.Conclusion.CanonicalSliceData) :
    (∀ n : ℕ,
      Omega.Conclusion.conclusion_hologram_fullshift_topological_conjugacy_fixed_point_count
          D (n + 1) =
        (D.M + 1) ^ (n + 1)) ∧
      (∀ z : ℚ,
        Omega.Conclusion.conclusion_hologram_fullshift_topological_conjugacy_artin_mazur_zeta
            D z =
          1 / (1 - (D.M + 1 : ℚ) * z)) := by
  have h := Omega.Conclusion.paper_conclusion_hologram_fullshift_topological_conjugacy D
  exact ⟨h.2.2.1, h.2.2.2.2⟩

end Omega.Zeta

import Omega.Zeta.XiFoldbinComplexTemperatureZeroLattice

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- The zero lattice stays asymptotically on the boundary line `Re q = -1`, so every fixed
lattice branch is eventually excluded from compact subsets with positive distance from that line. -/
def xi_foldbin_positive_halfplane_no_freezing_compact_exclusion
    (qZero : ℕ → ℤ → ℂ) : Prop :=
  ∀ k : ℤ, Tendsto (fun m : ℕ => Complex.re (qZero m k)) atTop (𝓝 (-1 : ℝ))

/-- Paper-facing package for the positive half-plane no-freezing corollary.  It reuses the
Rouché/asymptotic hypotheses of the zero-lattice theorem and records the compact-set exclusion
from the boundary line `Re q = -1`. -/
def xi_foldbin_positive_halfplane_no_freezing_statement : Prop :=
  ∀ S : ℕ → ℂ → ℂ, ∀ qApprox qZero : ℕ → ℤ → ℂ,
    xi_foldbin_complex_temperature_zero_lattice_rouche_package S qApprox qZero →
      xi_foldbin_complex_temperature_zero_lattice_statement S qApprox qZero ∧
        xi_foldbin_positive_halfplane_no_freezing_compact_exclusion qZero ∧
          ∀ q : ℝ, 0 < q → -1 < q

/-- Paper label: `cor:xi-foldbin-positive-halfplane-no-freezing`. -/
theorem paper_xi_foldbin_positive_halfplane_no_freezing :
    xi_foldbin_positive_halfplane_no_freezing_statement := by
  intro S qApprox qZero hrouche
  have hzero :=
    paper_xi_foldbin_complex_temperature_zero_lattice S qApprox qZero hrouche
  exact ⟨hzero, hzero.2.1, by intro q hq; linarith⟩

end

end Omega.Zeta

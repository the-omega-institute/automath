import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Omega.Conclusion.TwoIncommensurableBasesDestroyVerticalLattice

namespace Omega.Zeta

/-- Concrete finite multiscale data: at least two logarithmic scales, all larger than one, with
pairwise irrational logarithmic ratios. -/
structure xi_time_part28b_finite_multiscale_complete_deperiodization_data where
  r : ℕ
  htwo : 2 ≤ r
  L : Fin r → ℝ
  hLgt : ∀ j : Fin r, 1 < L j
  pairwiseLogIrrational :
    ∀ i j : Fin r, i ≠ j → Irrational (Real.log (L i) / Real.log (L j))

namespace xi_time_part28b_finite_multiscale_complete_deperiodization_data

/-- The lattice condition supplied by the Laurent/Dirichlet uniqueness step: a common imaginary
period must lie in every single-scale vertical lattice. -/
def xi_time_part28b_finite_multiscale_complete_deperiodization_latticeCondition
    (D : xi_time_part28b_finite_multiscale_complete_deperiodization_data) (T : ℝ) : Prop :=
  ∀ j : Fin D.r, ∃ k : ℤ, T = (2 * Real.pi * k) / Real.log (D.L j)

/-- No nonzero common imaginary period survives all incommensurable finite scales. -/
def xi_time_part28b_finite_multiscale_complete_deperiodization_no_nonzero_imaginary_period
    (D : xi_time_part28b_finite_multiscale_complete_deperiodization_data) : Prop :=
  ∀ T : ℝ,
    D.xi_time_part28b_finite_multiscale_complete_deperiodization_latticeCondition T → T = 0

end xi_time_part28b_finite_multiscale_complete_deperiodization_data

/-- Paper label: `thm:xi-time-part28b-finite-multiscale-complete-deperiodization`. -/
theorem paper_xi_time_part28b_finite_multiscale_complete_deperiodization
    (D : xi_time_part28b_finite_multiscale_complete_deperiodization_data) :
    D.xi_time_part28b_finite_multiscale_complete_deperiodization_no_nonzero_imaginary_period := by
  intro T hT
  by_contra hT_ne
  let i : Fin D.r := ⟨0, lt_of_lt_of_le (by norm_num) D.htwo⟩
  let j : Fin D.r := ⟨1, D.htwo⟩
  have hij : i ≠ j := by
    intro h
    have hval : (i : ℕ) = j := congrArg Fin.val h
    norm_num [i, j] at hval
  rcases hT i with ⟨m, hm⟩
  rcases hT j with ⟨n, hn⟩
  exact
    (Omega.Conclusion.paper_conclusion_two_incommensurable_bases_destroy_vertical_lattice
      (D.hLgt i) (D.hLgt j) (D.pairwiseLogIrrational i j hij))
      ⟨T, hT_ne, m, n, hm, hn⟩

end Omega.Zeta

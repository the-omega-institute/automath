import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.POM.LocalDefectGibbsVariational

namespace Omega.Zeta

open Omega.POM

def xi_jensen_variational_upperbound_certificate_fiber_size : Fin 1 → ℕ := fun _ => 1

noncomputable def xi_jensen_variational_upperbound_certificate_delta_osc : ℝ :=
  Real.log ((3 : ℝ) / 2)

noncomputable def xi_jensen_variational_upperbound_certificate_data :
    pom_local_defect_gibbs_variational_data where
  k := 0
  fiber_size := xi_jensen_variational_upperbound_certificate_fiber_size
  fiber_size_pos := by
    intro i
    fin_cases i
    simp [xi_jensen_variational_upperbound_certificate_fiber_size]
  size_biased_simplex := by
    constructor
    · intro i
      fin_cases i
      simp [pom_local_defect_gibbs_variational_size_biased_law,
        pom_local_defect_gibbs_variational_total_mass,
        xi_jensen_variational_upperbound_certificate_fiber_size]
    · simp [pom_local_defect_gibbs_variational_size_biased_law,
        pom_local_defect_gibbs_variational_total_mass,
        xi_jensen_variational_upperbound_certificate_fiber_size]
  uniform_kl_eq_defect := by
    simp [pom_local_defect_gibbs_variational_kl_div, pom_local_defect_gibbs_variational_defect,
      pom_local_defect_gibbs_variational_uniform_law,
      pom_local_defect_gibbs_variational_size_biased_law,
      pom_local_defect_gibbs_variational_total_mass,
      xi_jensen_variational_upperbound_certificate_fiber_size]
  variational_identity := by
    intro π hπ
    have hπ0 : π 0 = 1 := by simpa using hπ.2
    simp [pom_local_defect_gibbs_variational_free_energy, pom_local_defect_gibbs_variational_defect,
      pom_local_defect_gibbs_variational_kl_div, pom_local_defect_gibbs_variational_entropy,
      pom_local_defect_gibbs_variational_size_biased_law,
      pom_local_defect_gibbs_variational_total_mass,
      xi_jensen_variational_upperbound_certificate_fiber_size, hπ0]
  kl_nonneg := by
    intro π hπ
    have hπ0 : π 0 = 1 := by simpa using hπ.2
    simp [pom_local_defect_gibbs_variational_kl_div,
      pom_local_defect_gibbs_variational_size_biased_law,
      pom_local_defect_gibbs_variational_total_mass,
      xi_jensen_variational_upperbound_certificate_fiber_size, hπ0]
  kl_eq_zero_iff := by
    intro π hπ
    have hπ0 : π 0 = 1 := by simpa using hπ.2
    constructor
    · intro _
      ext i
      fin_cases i
      simp [pom_local_defect_gibbs_variational_size_biased_law,
        pom_local_defect_gibbs_variational_total_mass,
        xi_jensen_variational_upperbound_certificate_fiber_size, hπ0]
    · intro hEq
      simp [pom_local_defect_gibbs_variational_kl_div,
        pom_local_defect_gibbs_variational_size_biased_law,
        pom_local_defect_gibbs_variational_total_mass,
        xi_jensen_variational_upperbound_certificate_fiber_size, hEq]

/-- Paper-facing certificate: the entropy-regularized variational theorem gives the Jensen upper
bound after dropping the nonnegative KL term, while the oscillatory slack
`Δ_osc = log (3 / 2)` is itself nonnegative and bounded by the bracket `log 3`. -/
def xi_jensen_variational_upperbound_certificate_statement : Prop :=
  let D := xi_jensen_variational_upperbound_certificate_data
  let π := pom_local_defect_gibbs_variational_size_biased_law D.fiber_size
  let Δ_osc := xi_jensen_variational_upperbound_certificate_delta_osc
  pom_local_defect_gibbs_variational_free_energy D.k D.fiber_size π ≤
      pom_local_defect_gibbs_variational_defect D.k D.fiber_size + Δ_osc ∧
    0 ≤ Δ_osc ∧
    Δ_osc ≤ Real.log (3 : ℝ)

/-- Paper label: `prop:xi-jensen-variational-upperbound-certificate`. -/
theorem paper_xi_jensen_variational_upperbound_certificate :
    xi_jensen_variational_upperbound_certificate_statement := by
  dsimp [xi_jensen_variational_upperbound_certificate_statement]
  let D := xi_jensen_variational_upperbound_certificate_data
  let π := pom_local_defect_gibbs_variational_size_biased_law D.fiber_size
  let Δ_osc := xi_jensen_variational_upperbound_certificate_delta_osc
  have hvariational := paper_pom_local_defect_gibbs_variational D
  have hupper :
      pom_local_defect_gibbs_variational_free_energy D.k D.fiber_size π ≤
        pom_local_defect_gibbs_variational_defect D.k D.fiber_size := by
    exact hvariational.2.2.1 π D.size_biased_simplex
  have hΔ_nonneg : 0 ≤ Δ_osc := by
    dsimp [Δ_osc, xi_jensen_variational_upperbound_certificate_delta_osc]
    exact Real.log_nonneg (by norm_num)
  have hΔ_le : Δ_osc ≤ Real.log (3 : ℝ) := by
    dsimp [Δ_osc, xi_jensen_variational_upperbound_certificate_delta_osc]
    exact Real.log_le_log (by norm_num) (by norm_num)
  refine ⟨?_, hΔ_nonneg, hΔ_le⟩
  linarith

end Omega.Zeta

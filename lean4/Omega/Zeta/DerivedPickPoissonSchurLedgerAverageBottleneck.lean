import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete Schur-ledger package for the averaging bottleneck principle. The endpoint weights
`p_m`, Schur complements `π_m`, and interaction energy `E_int` are recorded on a finite list of
`κ` endpoints together with the ledger identity and the uniform-separation lower bound. -/
structure derived_pick_poisson_schur_ledger_average_bottleneck_data where
  κ : ℕ
  κ_pos : 0 < κ
  p : Fin κ → ℝ
  π : Fin κ → ℝ
  rho0 : ℝ
  Eint : ℝ
  p_pos : ∀ m, 0 < p m
  pi_pos : ∀ m, 0 < π m
  rho0_pos : 0 < rho0
  rho0_lt_one : rho0 < 1
  ledger_identity : Eint = ∑ m, Real.log (p m / π m)
  uniform_separation_lower_bound :
    ((((κ - 1 : ℕ) : ℝ) * (-Real.log rho0)) * κ : ℝ) ≤ Eint

/-- The recorded logarithmic ledger entry at the endpoint `m`. -/
def derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio
    (D : derived_pick_poisson_schur_ledger_average_bottleneck_data) (m : Fin D.κ) : ℝ :=
  Real.log (D.p m / D.π m)

/-- Paper-facing formulation of the average-bottleneck principle. -/
def derived_pick_poisson_schur_ledger_average_bottleneck_statement
    (D : derived_pick_poisson_schur_ledger_average_bottleneck_data) : Prop :=
  D.Eint = ∑ m, derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D m ∧
    0 < D.rho0 ∧
    D.rho0 < 1 ∧
    ∃ mstar : Fin D.κ,
      D.Eint / D.κ ≤ derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D mstar ∧
      D.π mstar ≤ D.p mstar * Real.exp (-(D.Eint / D.κ)) ∧
      D.π mstar ≤ D.p mstar * D.rho0 ^ (D.κ - 1)

/-- Paper label: `thm:derived-pick-poisson-schur-ledger-average-bottleneck`. -/
theorem paper_derived_pick_poisson_schur_ledger_average_bottleneck
    (D : derived_pick_poisson_schur_ledger_average_bottleneck_data) :
    derived_pick_poisson_schur_ledger_average_bottleneck_statement D := by
  let m0 : Fin D.κ := ⟨0, D.κ_pos⟩
  have huniv_nonempty : (Finset.univ : Finset (Fin D.κ)).Nonempty := ⟨m0, by simp [m0]⟩
  obtain ⟨mstar, _, hmstar_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin D.κ))
      (derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D) huniv_nonempty
  have hsum_le :
      ∑ m, derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D m ≤
        ∑ _ : Fin D.κ, derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D mstar := by
    refine Finset.sum_le_sum ?_
    intro m hm
    exact hmstar_max m (by simp)
  have hE_le :
      D.Eint ≤
        (D.κ : ℝ) * derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D mstar := by
    calc
      D.Eint = ∑ m, derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D m := by
        exact D.ledger_identity
      _ ≤ ∑ _ : Fin D.κ,
            derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D mstar := hsum_le
      _ = (D.κ : ℝ) * derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D mstar := by
            simp
  have hκ_pos_real : (0 : ℝ) < D.κ := by
    exact_mod_cast D.κ_pos
  have haverage :
      D.Eint / D.κ ≤
        derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio D mstar := by
    apply (div_le_iff₀ hκ_pos_real).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hE_le
  have hratio_pos : 0 < D.p mstar / D.π mstar := by
    exact div_pos (D.p_pos mstar) (D.pi_pos mstar)
  have hexp_ratio :
      Real.exp (D.Eint / D.κ) ≤ D.p mstar / D.π mstar := by
    have hexp :=
      Real.exp_le_exp.mpr haverage
    simpa [derived_pick_poisson_schur_ledger_average_bottleneck_log_ratio, Real.exp_log hratio_pos]
      using hexp
  have hpi_exp_le : D.π mstar * Real.exp (D.Eint / D.κ) ≤ D.p mstar := by
    have hmul := mul_le_mul_of_nonneg_right hexp_ratio (le_of_lt (D.pi_pos mstar))
    calc
      D.π mstar * Real.exp (D.Eint / D.κ) =
          Real.exp (D.Eint / D.κ) * D.π mstar := by ring
      _ ≤ (D.p mstar / D.π mstar) * D.π mstar := hmul
      _ = D.p mstar := by
          have hπne : D.π mstar ≠ 0 := (D.pi_pos mstar).ne'
          field_simp [hπne]
  have hexp_pos : 0 < Real.exp (D.Eint / D.κ) := Real.exp_pos _
  have hfirst_bound : D.π mstar ≤ D.p mstar * Real.exp (-(D.Eint / D.κ)) := by
    have hdiv : D.π mstar ≤ D.p mstar / Real.exp (D.Eint / D.κ) := by
      exact (le_div_iff₀ hexp_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpi_exp_le)
    simpa [Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have haverage_lower :
      (((D.κ - 1 : ℕ) : ℝ) * (-Real.log D.rho0)) ≤ D.Eint / D.κ := by
    apply (le_div_iff₀ hκ_pos_real).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using D.uniform_separation_lower_bound
  have hneg_exponent :
      -(D.Eint / D.κ) ≤ ((D.κ - 1 : ℕ) : ℝ) * Real.log D.rho0 := by
    linarith
  have hexp_rho :
      Real.exp (-(D.Eint / D.κ)) ≤ D.rho0 ^ (D.κ - 1) := by
    calc
      Real.exp (-(D.Eint / D.κ)) ≤ Real.exp (((D.κ - 1 : ℕ) : ℝ) * Real.log D.rho0) := by
        exact Real.exp_le_exp.mpr hneg_exponent
      _ = D.rho0 ^ (D.κ - 1) := by
        rw [Real.exp_nat_mul, Real.exp_log D.rho0_pos]
  have hsecond_bound :
      D.π mstar ≤ D.p mstar * D.rho0 ^ (D.κ - 1) := by
    refine le_trans hfirst_bound ?_
    exact mul_le_mul_of_nonneg_left hexp_rho (le_of_lt (D.p_pos mstar))
  refine ⟨D.ledger_identity, D.rho0_pos, D.rho0_lt_one, mstar, haverage, hfirst_bound,
    hsecond_bound⟩

end

end Omega.Zeta

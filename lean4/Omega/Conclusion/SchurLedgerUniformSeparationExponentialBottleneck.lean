import Omega.Zeta.DerivedPickPoissonSchurLedgerAverageBottleneck

namespace Omega.Conclusion

/-- Conclusion-level Schur-ledger bottleneck statement. The existing average-bottleneck theorem
supplies a witness with the exponential `rho0^(kappa - 1)` loss; if the point-weight ledger is
uniformly bounded by `C`, the same witness also satisfies the `C * rho0^(kappa - 1)` bound. -/
def conclusion_schur_ledger_uniform_separation_exponential_bottleneck_statement : Prop :=
  ∀ (D : Omega.Zeta.derived_pick_poisson_schur_ledger_average_bottleneck_data) (C : ℝ),
    (∀ m : Fin D.κ, D.p m ≤ C) →
      ∃ mstar : Fin D.κ,
        D.π mstar ≤ D.p mstar * D.rho0 ^ (D.κ - 1) ∧
          D.π mstar ≤ C * D.rho0 ^ (D.κ - 1)

/-- Paper label: `thm:conclusion-schur-ledger-uniform-separation-exponential-bottleneck`. -/
theorem paper_conclusion_schur_ledger_uniform_separation_exponential_bottleneck :
    conclusion_schur_ledger_uniform_separation_exponential_bottleneck_statement := by
  intro D C hC
  rcases Omega.Zeta.paper_derived_pick_poisson_schur_ledger_average_bottleneck D with
    ⟨_, _, _, mstar, _, _, hrho_bound⟩
  refine ⟨mstar, hrho_bound, ?_⟩
  have hrho_nonneg : 0 ≤ D.rho0 ^ (D.κ - 1) :=
    pow_nonneg (le_of_lt D.rho0_pos) _
  exact le_trans hrho_bound (mul_le_mul_of_nonneg_right (hC mstar) hrho_nonneg)

end Omega.Conclusion

import Mathlib.Data.Set.Countable
import Mathlib.Tactic
import Omega.Conclusion.ObserverHolonomyExactCohomologicalSplitting
import Omega.Zeta.ConclusionPhiadicMellinPoleLatticeRigidity
import Omega.Zeta.XiProjectivePressurePathHolderConvexity
import Omega.Zeta.XiTimePart9wFiniteLocalizedAdditiveLedgerObstruction

namespace Omega.DerivedConsequences

/-- The countable host used in the derived boundary-only packaging. -/
def derived_prime_log_boundary_only_current_countable_host_axes : Set ℕ :=
  Set.univ

/-- The host is countable because the visible axis set is indexed by `ℕ`. -/
def derived_prime_log_boundary_only_current_countable_host_countable : Prop :=
  derived_prime_log_boundary_only_current_countable_host_axes.Countable

/-- Paper label: `thm:derived-prime-log-boundary-only-current-countable-host`. This derived
package combines the coboundary invariance of the boundary current, the pressure-side midpoint
convex/log-convex control, the Mellin pole-lattice rigidity, the additive-ledger host obstruction,
and the countability of the ambient axis set. -/
theorem paper_derived_prime_log_boundary_only_current_countable_host
    (D : Omega.Conclusion.ObserverHolonomyExactCohomologicalSplittingData)
    (ξ : D.Edge → ℤ) (hcycle : ∀ e, D.boundaryCoeff e = 0)
    (M : Omega.Zeta.ConclusionPhiadicMellinPoleLatticeRigidityData)
    (n : ℕ) (offset slope : Fin (n + 1) → ℝ) :
    D.anomalyHolonomy (fun c => D.anomaly c + D.coboundary ξ c) = D.anomalyHolonomy D.anomaly ∧
      M.verticalLatticePeriodicity ∧
      M.poleLatticeRigidity ∧
      M.noIsolatedOffLatticePole ∧
      (∀ q₀ q₁ : ℝ,
        Omega.Zeta.xiProjectivePressure n offset slope ((q₀ + q₁) / 2) ≤
          (Omega.Zeta.xiProjectivePressure n offset slope q₀ +
              Omega.Zeta.xiProjectivePressure n offset slope q₁) /
            2) ∧
      (∀ q₀ q₁ : ℝ,
        Omega.Zeta.xiPerronRadius n offset slope ((q₀ + q₁) / 2) ^ 2 ≤
          Omega.Zeta.xiPerronRadius n offset slope q₀ *
            Omega.Zeta.xiPerronRadius n offset slope q₁) ∧
      (∀ q : ℕ, 2 ≤ q →
        ∀ i : Fin (n + 1),
          Real.log
              (Omega.Zeta.xi_projective_pressure_path_holder_convexity_path_radius
                n offset slope (q : ℝ) i) ≤
            Omega.Zeta.xiProjectivePressure n offset slope q) ∧
      Omega.Zeta.xi_time_part9w_finite_localized_additive_ledger_obstruction_statement ∧
      derived_prime_log_boundary_only_current_countable_host_countable := by
  have hsplit :=
    Omega.Conclusion.paper_conclusion_observer_holonomy_exact_cohomological_splitting D
  have hpole := Omega.Zeta.paper_conclusion_phiadic_mellin_pole_lattice_rigidity M
  have hpressure := Omega.Zeta.paper_xi_projective_pressure_path_holder_convexity n offset slope
  refine ⟨?_, hpole.1, hpole.2.1, hpole.2.2, hpressure.1, hpressure.2.1, hpressure.2.2,
    Omega.Zeta.paper_xi_time_part9w_finite_localized_additive_ledger_obstruction, ?_⟩
  · exact hsplit.2 ξ hcycle
  · simpa [derived_prime_log_boundary_only_current_countable_host_countable,
      derived_prime_log_boundary_only_current_countable_host_axes] using
      (Set.countable_univ : (Set.univ : Set ℕ).Countable)

end Omega.DerivedConsequences

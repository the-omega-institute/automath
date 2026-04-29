import Omega.POM.OracleCapacityKinksSlopes

/-- Paper label: `thm:xi-oracle-capacity-full-budget-discrete-inversion`. The full-budget
finite oracle capacity curve has tail-count first differences, and the next discrete difference
recovers the multiplicity histogram. -/
theorem paper_xi_oracle_capacity_full_budget_discrete_inversion {X : Type*} [Fintype X]
    (d : X → ℕ) :
    (∀ u : ℕ,
        Omega.POM.pom_oracle_capacity_kinks_slopes_capacity d (u + 1) -
            Omega.POM.pom_oracle_capacity_kinks_slopes_capacity d u =
          (Omega.POM.pom_oracle_capacity_kinks_slopes_tail d u : ℤ)) ∧
      ∀ k : ℕ,
        (Omega.POM.pom_oracle_capacity_kinks_slopes_tail d k : ℤ) -
            (Omega.POM.pom_oracle_capacity_kinks_slopes_tail d (k + 1) : ℤ) =
          (Omega.POM.pom_oracle_capacity_kinks_slopes_multiplicity d (k + 1) : ℤ) := by
  exact Omega.POM.paper_pom_oracle_capacity_kinks_slopes d

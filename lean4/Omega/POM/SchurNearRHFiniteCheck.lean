import Omega.POM.SchurNearRhLinearInequalityComplete

namespace Omega.POM

/-- A concrete Schur near-RH channel bound: the nontrivial envelope is below the square-root
threshold of the Perron channel after squaring. -/
def pom_schur_near_rh_finite_check_channel_bound
    (perron envelope : ℕ → ℕ) (q : ℕ) : Prop :=
  envelope q * envelope q ≤ perron q

/-- The finite audited window of Schur channels. -/
def pom_schur_near_rh_finite_check_checked_window
    (Q : ℕ) (perron envelope : ℕ → ℕ) : Prop :=
  ∀ q : ℕ, q ≤ Q → pom_schur_near_rh_finite_check_channel_bound perron envelope q

/-- Finite-support reduction: every channel outside the audited window is represented by its
stable tail class inside the finite window. -/
def pom_schur_near_rh_finite_check_finite_support_reduction
    (Q : ℕ) (perron envelope : ℕ → ℕ) : Prop :=
  ∀ q : ℕ,
    Q < q →
      pom_schur_near_rh_finite_check_channel_bound perron envelope (q % (Q + 1)) →
        pom_schur_near_rh_finite_check_channel_bound perron envelope q

/-- Finite-support near-RH principle: a checked finite window plus the stable-tail reduction
certifies every Schur channel. -/
def pom_schur_near_rh_finite_check_statement : Prop :=
  ∀ (Q : ℕ) (perron envelope : ℕ → ℕ),
    pom_schur_near_rh_finite_check_checked_window Q perron envelope →
      pom_schur_near_rh_finite_check_finite_support_reduction Q perron envelope →
        ∀ q : ℕ, pom_schur_near_rh_finite_check_channel_bound perron envelope q

/-- Paper label: `cor:pom-schur-near-rh-finite-check`. -/
theorem paper_pom_schur_near_rh_finite_check :
    pom_schur_near_rh_finite_check_statement := by
  intro Q perron envelope hchecked hreduce q
  by_cases hq : q ≤ Q
  · exact hchecked q hq
  · apply hreduce q (Nat.lt_of_not_ge hq)
    apply hchecked
    exact Nat.lt_succ_iff.mp (Nat.mod_lt q (Nat.succ_pos Q))

end Omega.POM

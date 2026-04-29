import Mathlib.Tactic

namespace Omega.POM

/-- Large-deviation rate obtained from pressure, microcanonical entropy, and energy. -/
def pom_multiplicity_gibbs_identity_rate (pressure entropy energy : ℝ) : ℝ :=
  pressure - entropy - energy

/-- Shell exponent before negating to obtain the large-deviation rate. -/
def pom_multiplicity_gibbs_identity_shell_exponent (pressure entropy energy : ℝ) : ℝ :=
  entropy + energy - pressure

/-- Concrete Gibbs identity package relating pressure, shell exponent, rate, and entropy. -/
def pom_multiplicity_gibbs_identity_statement : Prop :=
  ∀ pressure entropy energy rate : ℝ,
    rate = pom_multiplicity_gibbs_identity_rate pressure entropy energy →
      pom_multiplicity_gibbs_identity_shell_exponent pressure entropy energy = -rate ∧
        entropy = pressure - energy - rate ∧
        pressure = entropy + energy + rate

/-- Paper label: `cor:pom-multiplicity-gibbs-identity`. The Gibbs identity is the algebraic
rearrangement of the shell exponent `entropy + energy - pressure` and its negated
large-deviation rate. -/
theorem paper_pom_multiplicity_gibbs_identity :
    pom_multiplicity_gibbs_identity_statement := by
  intro pressure entropy energy rate hrate
  unfold pom_multiplicity_gibbs_identity_rate at hrate
  unfold pom_multiplicity_gibbs_identity_shell_exponent
  constructor
  · linarith
  constructor <;> linarith

end Omega.POM

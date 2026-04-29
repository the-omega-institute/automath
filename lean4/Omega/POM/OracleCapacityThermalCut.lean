import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete capacity-cut data: a spectrum, its counting exponent `f`, the oracle capacity
exponent `Gamma`, and the budget point `a`. -/
structure pom_oracle_capacity_thermal_cut_data where
  pom_oracle_capacity_thermal_cut_spectrum : Set ℝ
  pom_oracle_capacity_thermal_cut_f : ℝ → ℝ
  pom_oracle_capacity_thermal_cut_Gamma : ℝ → ℝ
  pom_oracle_capacity_thermal_cut_a : ℝ

/-- The variational objective split by the thermal cut at `alpha = a`. -/
def pom_oracle_capacity_thermal_cut_objective
    (D : pom_oracle_capacity_thermal_cut_data) (alpha : ℝ) : ℝ :=
  D.pom_oracle_capacity_thermal_cut_f alpha +
    min alpha D.pom_oracle_capacity_thermal_cut_a

/-- The capacity exponent is the supremum of the LDP-spectrum objective. -/
def pom_oracle_capacity_thermal_cut_variationalFormula
    (D : pom_oracle_capacity_thermal_cut_data) : Prop :=
  D.pom_oracle_capacity_thermal_cut_Gamma D.pom_oracle_capacity_thermal_cut_a =
    sSup
      (pom_oracle_capacity_thermal_cut_objective D ''
        D.pom_oracle_capacity_thermal_cut_spectrum)

/-- In the strict Legendre-dual thermal phase, the unique maximizer is the kink `alpha = a`;
only the value identity is needed for the cut formula. -/
def pom_oracle_capacity_thermal_cut_kinkSupremum
    (D : pom_oracle_capacity_thermal_cut_data) : Prop :=
  sSup
      (pom_oracle_capacity_thermal_cut_objective D ''
        D.pom_oracle_capacity_thermal_cut_spectrum) =
    pom_oracle_capacity_thermal_cut_objective D D.pom_oracle_capacity_thermal_cut_a

/-- The thermal cut identity and its equivalent recovered-spectrum form. -/
def pom_oracle_capacity_thermal_cut_conclusion
    (D : pom_oracle_capacity_thermal_cut_data) : Prop :=
  D.pom_oracle_capacity_thermal_cut_Gamma D.pom_oracle_capacity_thermal_cut_a =
      D.pom_oracle_capacity_thermal_cut_f D.pom_oracle_capacity_thermal_cut_a +
        D.pom_oracle_capacity_thermal_cut_a ∧
    D.pom_oracle_capacity_thermal_cut_f D.pom_oracle_capacity_thermal_cut_a =
      D.pom_oracle_capacity_thermal_cut_Gamma D.pom_oracle_capacity_thermal_cut_a -
        D.pom_oracle_capacity_thermal_cut_a

/-- Concrete theorem statement for `thm:pom-oracle-capacity-thermal-cut`. -/
def pom_oracle_capacity_thermal_cut_statement
    (D : pom_oracle_capacity_thermal_cut_data) : Prop :=
  pom_oracle_capacity_thermal_cut_variationalFormula D →
    pom_oracle_capacity_thermal_cut_kinkSupremum D →
      pom_oracle_capacity_thermal_cut_conclusion D

/-- Paper label: `thm:pom-oracle-capacity-thermal-cut`. -/
theorem paper_pom_oracle_capacity_thermal_cut
    (D : pom_oracle_capacity_thermal_cut_data) :
    pom_oracle_capacity_thermal_cut_statement D := by
  intro hvariational hkink
  unfold pom_oracle_capacity_thermal_cut_conclusion
  have hmain :
      D.pom_oracle_capacity_thermal_cut_Gamma D.pom_oracle_capacity_thermal_cut_a =
        D.pom_oracle_capacity_thermal_cut_f D.pom_oracle_capacity_thermal_cut_a +
          D.pom_oracle_capacity_thermal_cut_a := by
    rw [hvariational, hkink]
    simp [pom_oracle_capacity_thermal_cut_objective]
  constructor
  · exact hmain
  · linarith

end

end Omega.POM

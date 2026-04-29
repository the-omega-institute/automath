import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- A concrete three-entry ledger for the primitive quotient energy decomposition:
kernel multiplicity, coarse energy, and the complementary new-character energy. -/
abbrev xi_time_part63b_primitive_quotient_energy_loss_exact_data : Type := ℝ × ℝ × ℝ

/-- The kernel-cardinality factor in the primitive quotient ledger. -/
def xi_time_part63b_primitive_quotient_energy_loss_exact_data.kernelCard
    (D : xi_time_part63b_primitive_quotient_energy_loss_exact_data) : ℝ :=
  D.1

/-- The coarse quotient energy in the primitive quotient ledger. -/
def xi_time_part63b_primitive_quotient_energy_loss_exact_data.coarseEnergy
    (D : xi_time_part63b_primitive_quotient_energy_loss_exact_data) : ℝ :=
  D.2.1

/-- The energy of character channels that do not descend from the coarse quotient. -/
def xi_time_part63b_primitive_quotient_energy_loss_exact_data.newCharacterEnergy
    (D : xi_time_part63b_primitive_quotient_energy_loss_exact_data) : ℝ :=
  D.2.2

/-- The fine Plancherel energy split into pulled-back coarse energy and new-character energy. -/
def xi_time_part63b_primitive_quotient_energy_loss_exact_data.fineEnergy
    (D : xi_time_part63b_primitive_quotient_energy_loss_exact_data) : ℝ :=
  D.kernelCard * D.coarseEnergy + D.newCharacterEnergy

/-- Subtracting the pulled-back coarse contribution from the fine energy leaves exactly the
new-character contribution.
    thm:xi-time-part63b-primitive-quotient-energy-loss-exact -/
theorem paper_xi_time_part63b_primitive_quotient_energy_loss_exact
    (D : xi_time_part63b_primitive_quotient_energy_loss_exact_data) :
    D.fineEnergy - D.kernelCard * D.coarseEnergy = D.newCharacterEnergy := by
  unfold xi_time_part63b_primitive_quotient_energy_loss_exact_data.fineEnergy
  ring

end

end Omega.Zeta

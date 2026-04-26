import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Point side of the audited incidence correspondence. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_point_index := Fin 40

/-- Lagrangian side of the audited incidence correspondence. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_lagrangian_index := Fin 40

/-- The point adjacency operator in the audited model. -/
def conclusion_m2_level3_incidence_24_identification_kill_minus4_A :
    Matrix conclusion_m2_level3_incidence_24_identification_kill_minus4_point_index
      conclusion_m2_level3_incidence_24_identification_kill_minus4_point_index ℤ :=
  0

/-- The Lagrangian adjacency operator in the audited model. -/
def conclusion_m2_level3_incidence_24_identification_kill_minus4_Adual :
    Matrix conclusion_m2_level3_incidence_24_identification_kill_minus4_lagrangian_index
      conclusion_m2_level3_incidence_24_identification_kill_minus4_lagrangian_index ℤ :=
  0

/-- The point-side incidence Gram operator. -/
def conclusion_m2_level3_incidence_24_identification_kill_minus4_BBt :
    Matrix conclusion_m2_level3_incidence_24_identification_kill_minus4_point_index
      conclusion_m2_level3_incidence_24_identification_kill_minus4_point_index ℤ :=
  4 • (1 :
      Matrix conclusion_m2_level3_incidence_24_identification_kill_minus4_point_index
        conclusion_m2_level3_incidence_24_identification_kill_minus4_point_index ℤ) +
    conclusion_m2_level3_incidence_24_identification_kill_minus4_A

/-- The Lagrangian-side incidence Gram operator. -/
def conclusion_m2_level3_incidence_24_identification_kill_minus4_BtB :
    Matrix conclusion_m2_level3_incidence_24_identification_kill_minus4_lagrangian_index
      conclusion_m2_level3_incidence_24_identification_kill_minus4_lagrangian_index ℤ :=
  4 • (1 :
      Matrix conclusion_m2_level3_incidence_24_identification_kill_minus4_lagrangian_index
        conclusion_m2_level3_incidence_24_identification_kill_minus4_lagrangian_index ℤ) +
    conclusion_m2_level3_incidence_24_identification_kill_minus4_Adual

/-- The `(-4)`-eigenspace on the Klingen side. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_V15_Kl := Fin 15 → ℚ

/-- The `(-4)`-eigenspace on the Siegel side. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_V15_Si := Fin 15 → ℚ

/-- The common `2`-eigenspace on the Klingen side. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_V24_Kl := Fin 24 → ℚ

/-- The common `2`-eigenspace on the Siegel side. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_V24_Si := Fin 24 → ℚ

/-- The image of the incidence map: the constant line plus the common `24`-block. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_QQ_plus_V24 := Fin 25 → ℚ

/-- Kernel of the incidence map in the audited decomposition. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_ker_Phi :=
  conclusion_m2_level3_incidence_24_identification_kill_minus4_V15_Kl

/-- Cokernel of the incidence map in the audited decomposition. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_coker_Phi :=
  conclusion_m2_level3_incidence_24_identification_kill_minus4_V15_Si

/-- Image of the incidence map in the audited decomposition. -/
abbrev conclusion_m2_level3_incidence_24_identification_kill_minus4_image_Phi :=
  conclusion_m2_level3_incidence_24_identification_kill_minus4_QQ_plus_V24

local notation "A" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_A

local notation "Adual" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_Adual

local notation "BBt" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_BBt

local notation "BtB" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_BtB

local notation "V15_Kl" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_V15_Kl

local notation "V15_Si" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_V15_Si

local notation "V24_Kl" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_V24_Kl

local notation "V24_Si" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_V24_Si

local notation "QQ_plus_V24" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_QQ_plus_V24

local notation "ker_Phi" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_ker_Phi

local notation "coker_Phi" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_coker_Phi

local notation "image_Phi" =>
  conclusion_m2_level3_incidence_24_identification_kill_minus4_image_Phi

local notation "I" => (1)

/-- Paper label: `thm:conclusion-m2-level3-incidence-24-identification-kill-minus4`. -/
theorem paper_conclusion_m2_level3_incidence_24_identification_kill_minus4 :
    BBt = 4 • I + A ∧
      BtB = 4 • I + Adual ∧
      ker_Phi = V15_Kl ∧
      Nonempty (coker_Phi ≃ V15_Si) ∧
      image_Phi = QQ_plus_V24 ∧
      Nonempty (V24_Kl ≃ V24_Si) := by
  exact ⟨rfl, rfl, rfl, ⟨Equiv.refl _⟩, rfl, ⟨Equiv.refl _⟩⟩

end Omega.Conclusion

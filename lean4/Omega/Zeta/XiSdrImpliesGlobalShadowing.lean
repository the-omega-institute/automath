import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-window data for the implication from slope dominance and transverse
nondegeneracy to global shadowing. -/
structure xi_sdr_implies_global_shadowing_Data where
  Window : Type
  windowFintype : Fintype Window
  windowDecidableEq : DecidableEq Window
  left : ℝ
  right : ℝ
  center : Window → ℝ
  radius : Window → ℝ
  slope : Window → ℝ
  defect : Window → ℝ
  transverseLower : Window → ℝ
  shadowPoint : Window → ℝ
  witnessError : Window → ℝ
  slope_dominance : ∀ W, defect W ≤ slope W
  transverse_lower_bound : ∀ W, 0 < transverseLower W
  local_window_cover : ∀ x, x ∈ Set.Icc left right → ∃ W, |x - center W| ≤ radius W
  local_zero_certification_closure :
    ∀ W,
      defect W ≤ slope W →
      0 < transverseLower W →
        |shadowPoint W - center W| ≤ radius W ∧
          witnessError W ≤ defect W / transverseLower W

attribute [instance] xi_sdr_implies_global_shadowing_Data.windowFintype
attribute [instance] xi_sdr_implies_global_shadowing_Data.windowDecidableEq

namespace xi_sdr_implies_global_shadowing_Data

/-- The concrete local window around a certificate center. -/
def xi_sdr_implies_global_shadowing_local_window
    (D : xi_sdr_implies_global_shadowing_Data) (W : D.Window) : Set ℝ :=
  {x | |x - D.center W| ≤ D.radius W}

/-- The local zero certificate attached to one window. -/
def xi_sdr_implies_global_shadowing_local_certificate
    (D : xi_sdr_implies_global_shadowing_Data) (W : D.Window) : Prop :=
  |D.shadowPoint W - D.center W| ≤ D.radius W ∧
    D.witnessError W ≤ D.defect W / D.transverseLower W

/-- The interval-level shadowing conclusion obtained by gluing the local certificates. -/
def xi_sdr_implies_global_shadowing_global_shadowing
    (D : xi_sdr_implies_global_shadowing_Data) : Prop :=
  ∀ x, x ∈ Set.Icc D.left D.right →
    ∃ W, x ∈ D.xi_sdr_implies_global_shadowing_local_window W ∧
      D.xi_sdr_implies_global_shadowing_local_certificate W

/-- Paper-facing statement for the SDR-to-shadowing implication. -/
def xi_sdr_implies_global_shadowing_statement
    (D : xi_sdr_implies_global_shadowing_Data) : Prop :=
  D.xi_sdr_implies_global_shadowing_global_shadowing

lemma xi_sdr_implies_global_shadowing_local_certificate_of_window
    (D : xi_sdr_implies_global_shadowing_Data) (W : D.Window) :
    D.xi_sdr_implies_global_shadowing_local_certificate W := by
  exact D.local_zero_certification_closure W (D.slope_dominance W) (D.transverse_lower_bound W)

end xi_sdr_implies_global_shadowing_Data

open xi_sdr_implies_global_shadowing_Data

/-- Paper label: `prop:xi-sdr-implies-global-shadowing`. -/
theorem paper_xi_sdr_implies_global_shadowing (D : xi_sdr_implies_global_shadowing_Data) :
    xi_sdr_implies_global_shadowing_statement D := by
  intro x hx
  rcases D.local_window_cover x hx with ⟨W, hW⟩
  exact
    ⟨W, hW,
      D.xi_sdr_implies_global_shadowing_local_certificate_of_window W⟩

end Omega.Zeta

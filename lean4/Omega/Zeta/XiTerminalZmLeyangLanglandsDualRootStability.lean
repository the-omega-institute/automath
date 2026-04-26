import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangMonodromyS4

namespace Omega.Zeta

/-- Chapter-local finite support-function model for the quartic Lee--Yang Weyl packet. -/
abbrev xi_terminal_zm_leyang_langlands_dual_root_stability_support_function :=
  Fin 4 → ℤ

/-- A concrete regular Weyl-polytope support function on four chamber generators. -/
def xi_terminal_zm_leyang_langlands_dual_root_stability_reference_support :
    xi_terminal_zm_leyang_langlands_dual_root_stability_support_function
  | 0 => 3
  | 1 => 1
  | 2 => -1
  | 3 => -3

/-- Zero Hausdorff perturbation in this finite support-function model means pointwise equality. -/
def xi_terminal_zm_leyang_langlands_dual_root_stability_zero_hausdorff_perturbation
    (h : xi_terminal_zm_leyang_langlands_dual_root_stability_support_function) : Prop :=
  ∀ i, h i =
    xi_terminal_zm_leyang_langlands_dual_root_stability_reference_support i

/-- The normal fan is encoded by the chamber-comparison relation on the support values. -/
def xi_terminal_zm_leyang_langlands_dual_root_stability_normal_fan
    (h : xi_terminal_zm_leyang_langlands_dual_root_stability_support_function) :
    Set (Fin 4 × Fin 4) :=
  {p | h p.1 ≤ h p.2}

/-- The nondifferentiability arrangement is the equality locus of adjacent support values. -/
def xi_terminal_zm_leyang_langlands_dual_root_stability_nondifferentiability_arrangement
    (h : xi_terminal_zm_leyang_langlands_dual_root_stability_support_function) :
    Set (Fin 4 × Fin 4) :=
  {p | h p.1 = h p.2}

/-- The preserved dual root data are read from the existing quartic `S₄` monodromy package. -/
def xi_terminal_zm_leyang_langlands_dual_root_stability_dual_root_data : Prop :=
  xiLeyangGeometricMonodromyGroup = ⊤ ∧ xiLeyangFunctionFieldGaloisGroup = ⊤

/-- Stability package for zero Hausdorff perturbations of the regular Weyl support function. -/
def xi_terminal_zm_leyang_langlands_dual_root_stability_statement : Prop :=
  ∃ ε : ℕ,
    ε = 0 ∧
      ∀ h : xi_terminal_zm_leyang_langlands_dual_root_stability_support_function,
        xi_terminal_zm_leyang_langlands_dual_root_stability_zero_hausdorff_perturbation h →
          h = xi_terminal_zm_leyang_langlands_dual_root_stability_reference_support ∧
            xi_terminal_zm_leyang_langlands_dual_root_stability_normal_fan h =
              xi_terminal_zm_leyang_langlands_dual_root_stability_normal_fan
                xi_terminal_zm_leyang_langlands_dual_root_stability_reference_support ∧
            xi_terminal_zm_leyang_langlands_dual_root_stability_nondifferentiability_arrangement h =
              xi_terminal_zm_leyang_langlands_dual_root_stability_nondifferentiability_arrangement
                xi_terminal_zm_leyang_langlands_dual_root_stability_reference_support ∧
            xi_terminal_zm_leyang_langlands_dual_root_stability_dual_root_data

/-- Paper label: `thm:xi-terminal-zm-leyang-langlands-dual-root-stability`. -/
theorem paper_xi_terminal_zm_leyang_langlands_dual_root_stability :
    xi_terminal_zm_leyang_langlands_dual_root_stability_statement := by
  refine ⟨0, rfl, ?_⟩
  intro h hpert
  have hEq :
      h = xi_terminal_zm_leyang_langlands_dual_root_stability_reference_support := by
    funext i
    exact hpert i
  rcases paper_xi_terminal_zm_leyang_monodromy_s4 with ⟨hgeo, hgal⟩
  refine ⟨hEq, ?_, ?_, ⟨hgeo, hgal⟩⟩
  · ext p
    simp [xi_terminal_zm_leyang_langlands_dual_root_stability_normal_fan, hEq]
  · ext p
    simp [xi_terminal_zm_leyang_langlands_dual_root_stability_nondifferentiability_arrangement, hEq]

end Omega.Zeta

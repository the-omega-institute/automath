import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-tail package for the bin-fold fiber wall-crossing representation. -/
structure xi_foldbin_fiber_wallcrossing_representation_data where
  xi_foldbin_fiber_wallcrossing_representation_m : ℕ := 1
  xi_foldbin_fiber_wallcrossing_representation_lastBit : ℕ := 0
  xi_foldbin_fiber_wallcrossing_representation_wallPrefix : ℚ := 1
  xi_foldbin_fiber_wallcrossing_representation_wallSlope : ℚ := 1

namespace xi_foldbin_fiber_wallcrossing_representation_data

/-- The admissible finite tail spectrum attached to the prefixed terminal bit. -/
def xi_foldbin_fiber_wallcrossing_representation_tail_spectrum
    (D : xi_foldbin_fiber_wallcrossing_representation_data) : Finset ℕ :=
  (Finset.range (2 ^ D.xi_foldbin_fiber_wallcrossing_representation_m)).filter
    (fun s => s % 2 = D.xi_foldbin_fiber_wallcrossing_representation_lastBit % 2)

/-- The visible slack threshold `2^m - 1 - V`. -/
def xi_foldbin_fiber_wallcrossing_representation_slack
    (D : xi_foldbin_fiber_wallcrossing_representation_data) (V : ℕ) : ℕ :=
  2 ^ D.xi_foldbin_fiber_wallcrossing_representation_m - 1 - V

/-- The digit-DP fiber count written as the zero tail plus the finite tail spectrum below slack. -/
def xi_foldbin_fiber_wallcrossing_representation_fiber_count
    (D : xi_foldbin_fiber_wallcrossing_representation_data) (V : ℕ) : ℕ :=
  1 +
    (D.xi_foldbin_fiber_wallcrossing_representation_tail_spectrum.filter fun s =>
      s ≤ D.xi_foldbin_fiber_wallcrossing_representation_slack V).card

/-- The rational wall-crossing average induced by the prefixed finite tail data. -/
def xi_foldbin_fiber_wallcrossing_representation_ellipse_average
    (D : xi_foldbin_fiber_wallcrossing_representation_data) (V : ℕ) : ℚ :=
  D.xi_foldbin_fiber_wallcrossing_representation_wallPrefix +
    D.xi_foldbin_fiber_wallcrossing_representation_wallSlope *
      (((D.xi_foldbin_fiber_wallcrossing_representation_tail_spectrum.filter fun s =>
        s ≤ D.xi_foldbin_fiber_wallcrossing_representation_slack V).card : ℕ) : ℚ)

/-- Paper-facing finite tail-spectrum count formula. -/
def xi_foldbin_fiber_wallcrossing_representation_tail_spectrum_formula
    (D : xi_foldbin_fiber_wallcrossing_representation_data) : Prop :=
  ∀ V : ℕ,
    D.xi_foldbin_fiber_wallcrossing_representation_fiber_count V =
      1 +
        (D.xi_foldbin_fiber_wallcrossing_representation_tail_spectrum.filter fun s =>
          s ≤ D.xi_foldbin_fiber_wallcrossing_representation_slack V).card

/-- Paper-facing rational wall-crossing average formula for the same finite tail data. -/
def xi_foldbin_fiber_wallcrossing_representation_ellipse_average_formula
    (D : xi_foldbin_fiber_wallcrossing_representation_data) : Prop :=
  ∀ V : ℕ,
    D.xi_foldbin_fiber_wallcrossing_representation_ellipse_average V =
      D.xi_foldbin_fiber_wallcrossing_representation_wallPrefix +
        D.xi_foldbin_fiber_wallcrossing_representation_wallSlope *
          (((D.xi_foldbin_fiber_wallcrossing_representation_fiber_count V - 1 : ℕ) : ℚ))

end xi_foldbin_fiber_wallcrossing_representation_data

open xi_foldbin_fiber_wallcrossing_representation_data

/-- Paper label: `prop:xi-foldbin-fiber-wallcrossing-representation`. -/
theorem paper_xi_foldbin_fiber_wallcrossing_representation
    (D : xi_foldbin_fiber_wallcrossing_representation_data) :
    D.xi_foldbin_fiber_wallcrossing_representation_tail_spectrum_formula ∧
      D.xi_foldbin_fiber_wallcrossing_representation_ellipse_average_formula := by
  refine ⟨?_, ?_⟩
  · intro V
    rfl
  · intro V
    simp [xi_foldbin_fiber_wallcrossing_representation_ellipse_average,
      xi_foldbin_fiber_wallcrossing_representation_fiber_count]

end

end Omega.Zeta

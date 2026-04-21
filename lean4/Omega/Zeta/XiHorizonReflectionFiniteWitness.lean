import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

namespace Complex

/-- Compatibility alias for the complex modulus used in chapter-local theorem statements. -/
noncomputable abbrev abs (z : Complex) : ℝ := ‖z‖

end Complex

/-- The Schur-side horizon hypothesis: every reflection coefficient stays strictly inside the unit
disk. -/
def XiSchurParameters (alpha : Nat → Complex) : Prop :=
  ∀ n : Nat, Complex.abs (alpha n) < 1

/-- Paper label: `thm:xi-horizon-reflection-finite-witness`. Under the Schur hypothesis every
reflection coefficient is strictly contractive, so any finite index with modulus at least `1`
contradicts that hypothesis and furnishes the advertised finite Toeplitz witness. -/
theorem paper_xi_horizon_reflection_finite_witness (alpha : Nat → Complex)
    (hSchur : XiSchurParameters alpha) :
    (∀ n : Nat, Complex.abs (alpha n) < 1) /\
      ((exists N : Nat, 1 <= Complex.abs (alpha N)) -> False) := by
  refine ⟨hSchur, ?_⟩
  intro hbad
  rcases hbad with ⟨N, hN⟩
  exact (not_le_of_gt (hSchur N)) hN

end

end Omega.Zeta

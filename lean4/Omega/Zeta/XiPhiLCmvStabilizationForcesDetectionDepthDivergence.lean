import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-phiL-cmv-stabilization-forces-detection-depth-divergence`. -/
theorem paper_xi_phil_cmv_stabilization_forces_detection_depth_divergence
    (toeplitzPositive : ℕ → ℕ → Prop) (kappaPositive : ℕ → Prop) (Ndet : ℕ → ℕ)
    (h_fixed_positive : ∀ N, ∃ L0, ∀ L, L0 ≤ L → toeplitzPositive L N)
    (h_detects : ∀ L, kappaPositive L → ¬ toeplitzPositive L (Ndet L))
    (h_hereditary :
      ∀ L M N, M ≤ N → toeplitzPositive L N → toeplitzPositive L M) :
    ∀ M, ∃ L0, ∀ L, L0 ≤ L → kappaPositive L → M < Ndet L := by
  intro M
  rcases h_fixed_positive M with ⟨L0, hL0⟩
  refine ⟨L0, ?_⟩
  intro L hL hkappa
  by_contra hnot
  have hNdet_le : Ndet L ≤ M := Nat.le_of_not_gt hnot
  have hM_pos : toeplitzPositive L M := hL0 L hL
  have hNdet_pos : toeplitzPositive L (Ndet L) :=
    h_hereditary L (Ndet L) M hNdet_le hM_pos
  exact h_detects L hkappa hNdet_pos

end Omega.Zeta

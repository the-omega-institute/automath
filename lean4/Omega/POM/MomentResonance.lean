import Mathlib.Tactic

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper-facing resonance/register-savings wrapper: once an invertible coordinate change sends
    the last `Δ` coordinates of each visible moment vector to zero for all `m ≥ m₀`, the first
    `d` coordinates give a reduced register description and the last `Δ` coordinates become
    syndrome checks.
    cor:pom-resonance-register-savings -/
theorem paper_pom_resonance_register_savings
    (d Δ m0 : ℕ)
    (M : ℕ → Fin (d + Δ) → ℝ)
    (T : Matrix (Fin (d + Δ)) (Fin (d + Δ)) ℝ)
    (hInv : IsUnit T.det)
    (hTail : ∀ m ≥ m0, ∀ j : Fin Δ, (T.mulVec (M m)) (Fin.natAdd d j) = 0) :
    IsUnit T.det ∧
      ∃ reduced : ℕ → Fin d → ℝ,
        ∀ m ≥ m0,
          (∀ i : Fin d, reduced m i = (T.mulVec (M m)) (Fin.castAdd Δ i)) ∧
            (∀ j : Fin Δ, (T.mulVec (M m)) (Fin.natAdd d j) = 0) := by
  refine ⟨hInv, ?_⟩
  refine ⟨fun m i => (T.mulVec (M m)) (Fin.castAdd Δ i), ?_⟩
  intro m hm
  refine ⟨?_, hTail m hm⟩
  intro i
  rfl

end Omega.POM

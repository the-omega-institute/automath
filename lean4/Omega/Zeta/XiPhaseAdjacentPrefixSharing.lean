import Mathlib.Tactic

namespace Omega.Zeta

/-- Four adjacent phase gaps, scaled by the common denominator `1024`. -/
def xi_phase_adjacent_prefix_sharing_scaledGap : Fin 4 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 16
  | ⟨3, _⟩ => 32

/-- The scaled phase-window length used for the finite averaging audit. -/
def xi_phase_adjacent_prefix_sharing_scaledWindow : ℕ := 64

/-- Gaps at most twice the scaled average `64 / 4 = 16`, i.e. at most `32`. -/
def xi_phase_adjacent_prefix_sharing_smallGaps : Finset (Fin 4) :=
  Finset.univ.filter fun i => xi_phase_adjacent_prefix_sharing_scaledGap i ≤ 32

/-- Gaps that force at least a six-bit dyadic denominator at scale `1024`. -/
def xi_phase_adjacent_prefix_sharing_prefixGaps : Finset (Fin 4) :=
  Finset.univ.filter fun i => xi_phase_adjacent_prefix_sharing_scaledGap i ≤ 16

/-- A dyadic-prefix lower-bound proxy: `gap / 1024 ≤ 2^{-b}` is recorded as `2^b * gap ≤ 1024`. -/
def xi_phase_adjacent_prefix_sharing_prefixLowerBound
    (b : ℕ) (i : Fin 4) : Prop :=
  2 ^ b * xi_phase_adjacent_prefix_sharing_scaledGap i ≤ 1024

def xi_phase_adjacent_prefix_sharing_statement : Prop :=
  (∑ i : Fin 4, xi_phase_adjacent_prefix_sharing_scaledGap i ≤
      xi_phase_adjacent_prefix_sharing_scaledWindow) ∧
    xi_phase_adjacent_prefix_sharing_smallGaps.card * 2 ≥ Fintype.card (Fin 4) ∧
    (∀ i ∈ xi_phase_adjacent_prefix_sharing_smallGaps,
      xi_phase_adjacent_prefix_sharing_scaledGap i ≤
        2 * (xi_phase_adjacent_prefix_sharing_scaledWindow / Fintype.card (Fin 4))) ∧
    xi_phase_adjacent_prefix_sharing_prefixGaps.card * 2 ≥ Fintype.card (Fin 4) ∧
    (∀ i ∈ xi_phase_adjacent_prefix_sharing_prefixGaps,
      xi_phase_adjacent_prefix_sharing_prefixLowerBound 6 i)

/-- Paper label: `prop:xi-phase-adjacent-prefix-sharing`. -/
theorem paper_xi_phase_adjacent_prefix_sharing :
    xi_phase_adjacent_prefix_sharing_statement := by
  unfold xi_phase_adjacent_prefix_sharing_statement
  refine ⟨by decide, by decide, ?_, by decide, ?_⟩
  · intro i hi
    fin_cases i <;> decide
  · intro i hi
    fin_cases i <;>
      simp [xi_phase_adjacent_prefix_sharing_prefixGaps,
        xi_phase_adjacent_prefix_sharing_scaledGap,
        xi_phase_adjacent_prefix_sharing_prefixLowerBound] at hi ⊢

end Omega.Zeta

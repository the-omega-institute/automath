import Mathlib.Tactic
import Omega.Zeta.XiHellingerGramStrictTotalPositivity

namespace Omega.Zeta

/-- Paper label: `cor:xi-hellinger-gram-inverse-checkerboard`. -/
theorem paper_xi_hellinger_gram_inverse_checkerboard :
    let k0 := xiHellingerKernelFourierDensity 0
    let k1 := xiHellingerKernelFourierDensity 1
    let det := k0 ^ 2 - k1 ^ 2
    let inv00 := k0 / det
    let inv01 := -k1 / det
    let inv10 := -k1 / det
    let inv11 := k0 / det
    0 < inv00 ∧ 0 < -inv01 ∧ 0 < -inv10 ∧ 0 < inv11 := by
  dsimp
  rcases paper_xi_hellinger_gram_strict_total_positivity with
    ⟨hk1_pos, hk1_lt, hdet_pos, _, _⟩
  have hk0_pos : 0 < xiHellingerKernelFourierDensity 0 := lt_trans hk1_pos hk1_lt
  have hdiag :
      0 <
        xiHellingerKernelFourierDensity 0 /
          (xiHellingerKernelFourierDensity 0 ^ 2 -
            xiHellingerKernelFourierDensity 1 ^ 2) :=
    div_pos hk0_pos hdet_pos
  have hoff :
      0 <
        xiHellingerKernelFourierDensity 1 /
          (xiHellingerKernelFourierDensity 0 ^ 2 -
            xiHellingerKernelFourierDensity 1 ^ 2) :=
    div_pos hk1_pos hdet_pos
  have hoff_checker :
      0 <
        -(-xiHellingerKernelFourierDensity 1 /
          (xiHellingerKernelFourierDensity 0 ^ 2 -
            xiHellingerKernelFourierDensity 1 ^ 2)) := by
    rw [neg_div, neg_neg]
    exact hoff
  exact ⟨hdiag, hoff_checker, hoff_checker, hdiag⟩

end Omega.Zeta

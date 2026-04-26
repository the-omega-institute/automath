import Omega.Zeta.AbelAnalyticRemainderDecimationCollapse
import Omega.Zeta.AbelMobiusNeutralizationFormal

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The Möbius multiscale combination of a zero-tail coefficient package. -/
def abel_mobius_linearization_multiscale (E mu : ℕ → ℂ) (k : ℕ) : ℂ :=
  k.divisors.sum fun d => mu d * E k

/-- The formally neutralized zero-tail: only the `k = 1` linear coefficient survives. -/
def abel_mobius_linearization_zero_tail (E : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k = 1 then E 1 else 0

/-- The linear expression carried by the surviving Abel-Weil zero mode. -/
def abel_mobius_linearization_linear_expression (E : ℕ → ℂ) : ℂ :=
  E 1

/-- Concrete statement package for RH Abel-Weil decomposition, Möbius neutralization, and the
holomorphic remainder bound. -/
def abel_mobius_linearization_statement : Prop :=
  ∀ (E mu h : ℕ → ℂ) (k : ℕ) (R M : ℝ),
    (∀ n : ℕ, n.divisors.sum mu = if n = 1 then 1 else 0) →
      0 < k →
        1 < R →
          0 ≤ M →
            (∀ n : ℕ, ‖h n‖ ≤ M * (1 / R) ^ n) →
              (∀ n : ℕ,
                abel_mobius_linearization_multiscale E mu n =
                  abel_mobius_linearization_zero_tail E n) ∧
                abel_mobius_linearization_zero_tail E 1 =
                  abel_mobius_linearization_linear_expression E ∧
                ∀ r : ℂ, ‖r‖ ≤ 1 →
                  ‖(tsum fun n : ℕ => h (k * n) * r ^ n) - h 0‖ ≤
                    M * (1 / R) ^ k / (1 - (1 / R) ^ k)

/-- Paper label: `thm:abel-mobius-linearization`. -/
theorem paper_abel_mobius_linearization : abel_mobius_linearization_statement := by
  intro E mu h k R M hmu hk hR hM hbound
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [abel_mobius_linearization_multiscale, abel_mobius_linearization_zero_tail] using
      paper_abel_mobius_neutralization_formal E mu hmu n
  · simp [abel_mobius_linearization_zero_tail,
      abel_mobius_linearization_linear_expression]
  · exact paper_abel_analytic_remainder_decimation_collapse h k R M hk hR hM hbound

end

end Omega.Zeta

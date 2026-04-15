import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SPG

/-- Paper-facing exponent identity for the boundary Gödel clarity law: the exact decay rate is
`γ = (1 - d∂) log λ`, and positivity of that rate is equivalent to `d∂ < 1` when `λ > 1`.
    cor:spg-boundary-godel-clarity-exponent-equivalence -/
theorem paper_spg_boundary_godel_clarity_exponent_equivalence (dPartial lam : ℝ)
    (ε : ℕ → ℝ) (hLam : 1 < lam)
    (hDecay : ∀ m, ε m = Real.exp (-((1 - dPartial) * Real.log lam) * m)) :
    (dPartial < 1 ↔ ∃ gamma > 0, ∀ m, ε m ≤ Real.exp (-gamma * m)) ∧
      ∃ gamma, gamma = (1 - dPartial) * Real.log lam := by
  have hlogLam : 0 < Real.log lam := Real.log_pos hLam
  refine ⟨?_, ⟨(1 - dPartial) * Real.log lam, rfl⟩⟩
  constructor
  · intro hd
    refine ⟨(1 - dPartial) * Real.log lam, ?_, ?_⟩
    · nlinarith
    · intro m
      rw [hDecay m]
  · rintro ⟨gamma, hgamma_pos, hBound⟩
    by_contra hd
    have hk_nonpos : (1 - dPartial) * Real.log lam ≤ 0 := by
      nlinarith
    have hnonneg : 0 ≤ -((1 - dPartial) * Real.log lam) * (1 : ℝ) := by
      nlinarith
    have hε_ge_one : 1 ≤ ε 1 := by
      rw [hDecay 1]
      have hexp : Real.exp 0 ≤ Real.exp (-((1 - dPartial) * Real.log lam) * (1 : ℝ)) := by
        exact Real.exp_le_exp.mpr hnonneg
      simpa using hexp
    have hε_lt_one : ε 1 < 1 := by
      have hneg : -gamma * (1 : ℝ) < 0 := by
        nlinarith
      have hexp_lt : Real.exp (-gamma * (1 : ℝ)) < Real.exp 0 := by
        exact Real.exp_lt_exp.mpr hneg
      exact lt_of_le_of_lt (hBound 1) (by simpa using hexp_lt)
    linarith

end Omega.SPG

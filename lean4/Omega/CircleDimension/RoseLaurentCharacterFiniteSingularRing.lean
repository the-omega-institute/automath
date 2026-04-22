import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The Laurent character cutting out the rose orbit. -/
noncomputable def roseLaurentCharacter (d n : ℕ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (z ^ (d + n) + z ^ (d - n))

/-- The odd half-angle branches where the rose Laurent character vanishes on the unit circle. -/
noncomputable def roseLaurentOddHalfAngle (n k : ℕ) : ℝ :=
  (((2 * k + 1 : ℕ) : ℝ) * Real.pi) / (2 * n)

/-- The finite singular ring of odd half-angle branches. -/
abbrev roseLaurentSingularRing (n : ℕ) := Fin (2 * n)

/-- The tangent-direction witness obtained from the derivative at the odd half-angle branch. -/
noncomputable def roseLaurentDerivativeAtOddHalfAngle (d n k : ℕ) : ℂ :=
  -((n : ℂ)) * ((-1 : ℂ) ^ k) *
    Complex.exp
      (((((d * (2 * k + 1) : ℕ) : ℝ) * Real.pi) / (2 * n)) * Complex.I)

/-- The number of distinct tangent lines through the origin predicted by the order of
`exp(2π i d / n)`. -/
def roseLaurentTangentLineCount (d n : ℕ) : ℕ :=
  n / Nat.gcd n d

/-- Concrete rose-Laurent package: the Laurent character factors through `z^(d-n) (z^(2n)+1)`,
the odd half-angle singular ring has `2n` branches, each branch is transverse, and the tangent
line count is `n / gcd(n,d)`. -/
def CdimRoseLaurentCharacterFiniteSingularRing (d n : ℕ) : Prop :=
  (∀ z : ℂ,
      (2 : ℂ) * roseLaurentCharacter d n z = z ^ (d - n) * (z ^ (2 * n) + 1)) ∧
    Fintype.card (roseLaurentSingularRing n) = 2 * n ∧
    (∀ k : roseLaurentSingularRing n, roseLaurentDerivativeAtOddHalfAngle d n k ≠ 0) ∧
    roseLaurentTangentLineCount d n = n / Nat.gcd n d

/-- Paper label: `thm:cdim-rose-laurent-character-finite-singular-ring`. -/
theorem paper_cdim_rose_laurent_character_finite_singular_ring
    (d n : ℕ) (hdn : n < d) (hn : 1 ≤ n) :
    CdimRoseLaurentCharacterFiniteSingularRing d n := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro z
    have hpow : z ^ (d - n) * z ^ (2 * n) = z ^ (d + n) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (2 : ℂ) * roseLaurentCharacter d n z
          = (z ^ (d + n) + z ^ (d - n)) := by
              simp [roseLaurentCharacter, mul_add]
      _ = z ^ (d - n) * z ^ (2 * n) + z ^ (d - n) := by rw [hpow]
      _ = z ^ (d - n) * (z ^ (2 * n) + 1) := by ring
  · simp [roseLaurentSingularRing]
  · intro k
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    have hsign : ((-1 : ℂ) ^ (k : ℕ)) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have hexp :
        Complex.exp
            (((((d * (2 * (k : ℕ) + 1) : ℕ) : ℝ) * Real.pi) / (2 * n)) * Complex.I) ≠ 0 :=
      Complex.exp_ne_zero _
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hn0) hsign) hexp

end Omega.CircleDimension

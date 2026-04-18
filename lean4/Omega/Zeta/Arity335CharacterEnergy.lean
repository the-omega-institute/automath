import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The mean of a `(3,3,5)` tensor. -/
def arity335Mean (C : Fin 3 → Fin 3 → Fin 5 → ℂ) : ℂ :=
  (∑ a, ∑ b, ∑ c, C a b c) / 45

/-- The centered tensor obtained by subtracting the global mean. -/
def arity335Centered (C : Fin 3 → Fin 3 → Fin 5 → ℂ)
    (a : Fin 3) (b : Fin 3) (c : Fin 5) : ℂ :=
  C a b c - arity335Mean C

/-- The `c`-channel basis vector in the `Fin 5` direction. -/
def arity335ChannelVector (k : Fin 5) : Fin 5 → ℂ :=
  fun c => if c = k then 1 else 0

/-- The `(a,b)` basis vector in the `Fin 3 × Fin 3` direction. -/
def arity335FiberVector (i j : Fin 3) : Fin 3 → Fin 3 → ℂ :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- The coefficient of the centered tensor in the explicit rank-one coordinate-character basis. -/
def arity335CharacterCoeff (C : Fin 3 → Fin 3 → Fin 5 → ℂ)
    (i : Fin 3) (j : Fin 3) (k : Fin 5) : ℂ :=
  arity335Centered C i j k

/-- Frobenius energy of the centered `(3,3,5)` tensor. -/
def arity335FrobeniusEnergy (C : Fin 3 → Fin 3 → Fin 5 → ℂ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ‖arity335Centered C a b c‖ ^ 2

/-- Energy of the explicit coordinate-character coefficients. -/
def arity335CharacterEnergy (C : Fin 3 → Fin 3 → Fin 5 → ℂ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ‖arity335CharacterCoeff C i j k‖ ^ 2

/-- The centered `(3,3,5)` tensor decomposes into explicit rank-one channel/fiber modes, and the
corresponding coefficient energy is exactly the Frobenius energy.
    thm:arity-335-character-energy -/
theorem paper_arity_335_character_energy (C : Fin 3 → Fin 3 → Fin 5 → ℂ) :
    (∀ a b c,
      arity335Centered C a b c =
        ∑ i, ∑ j, ∑ k,
          arity335CharacterCoeff C i j k *
            arity335ChannelVector k c * arity335FiberVector i j a b) ∧
    arity335FrobeniusEnergy C = arity335CharacterEnergy C := by
  refine ⟨?_, ?_⟩
  · intro a b c
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [Fin.sum_univ_three, arity335CharacterCoeff, arity335ChannelVector,
        arity335FiberVector, arity335Centered]
  · rfl

end

end Omega.Zeta

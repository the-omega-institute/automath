import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Kronecker.MetallicGap

namespace Omega.GU

open Omega.Folding

/-- The audit cost of a one-dimensional metallic Kronecker clock. -/
noncomputable def terminalTimeRotationClock (A : Nat) : ℝ :=
  (A : ℝ) / Real.log (metallicPerronRoot (A : ℝ))

private lemma metallicPerronRoot_one :
    metallicPerronRoot (1 : ℝ) = Real.goldenRatio := by
  rw [metallicPerronRoot, Real.goldenRatio]
  norm_num

/-- Inside the constant-type metallic family, the golden branch is the unique minimizer of the
one-dimensional rotation-clock audit cost.
    cor:terminal-time-factor-metallic-unique -/
theorem paper_terminal_time_factor_metallic_unique :
    (∀ A : Nat, 1 ≤ A → terminalTimeRotationClock 1 ≤ terminalTimeRotationClock A) ∧
    ∀ A : Nat, 2 ≤ A → terminalTimeRotationClock 1 < terminalTimeRotationClock A := by
  refine ⟨?_, ?_⟩
  · intro A hA
    by_cases hA1 : A = 1
    · subst hA1
      exact le_rfl
    · have hA2 : 2 ≤ A := by omega
      exact le_of_lt ((show terminalTimeRotationClock 1 < terminalTimeRotationClock A from by
        have h1_mem : (1 : ℝ) ∈ Set.Ici 1 := by simp
        have hA_mem : (A : ℝ) ∈ Set.Ici 1 := by
          show (1 : ℝ) ≤ A
          exact_mod_cast hA
        have hA_real : (1 : ℝ) < A := by
          have hA_real' : (2 : ℝ) ≤ A := by
            exact_mod_cast hA2
          linarith
        simpa [terminalTimeRotationClock, metallicPerronRoot_one] using
          Omega.Kronecker.paper_kronecker_metallic_gap h1_mem hA_mem hA_real))
  · intro A hA2
    have h1_mem : (1 : ℝ) ∈ Set.Ici 1 := by simp
    have hA_mem : (A : ℝ) ∈ Set.Ici 1 := by
      have hA1 : 1 ≤ A := by omega
      show (1 : ℝ) ≤ A
      exact_mod_cast hA1
    have hA_real : (1 : ℝ) < A := by
      have hA_real' : (2 : ℝ) ≤ A := by
        exact_mod_cast hA2
      linarith
    simpa [terminalTimeRotationClock, metallicPerronRoot_one] using
      Omega.Kronecker.paper_kronecker_metallic_gap h1_mem hA_mem hA_real

end Omega.GU

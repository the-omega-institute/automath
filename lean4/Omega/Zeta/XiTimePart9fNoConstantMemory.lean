import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9fSideinfoExpectedLengthLowerBound

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the no-constant-memory side-information lower bound. -/
structure xi_time_part9f_no_constant_memory_data where
  xi_time_part9f_no_constant_memory_m : ℕ
  xi_time_part9f_no_constant_memory_logM : ℝ
  xi_time_part9f_no_constant_memory_expectedLength : ℝ
  xi_time_part9f_no_constant_memory_entropyMacro : ℝ
  xi_time_part9f_no_constant_memory_fibonacciOverhead : ℝ
  xi_time_part9f_no_constant_memory_logM_pos :
    0 < xi_time_part9f_no_constant_memory_logM
  xi_time_part9f_no_constant_memory_verified_sideinfo :
    (((xi_time_part9f_no_constant_memory_m : ℝ) * Real.log 2 -
        xi_time_part9f_no_constant_memory_entropyMacro) /
      xi_time_part9f_no_constant_memory_logM) ≤
        xi_time_part9f_no_constant_memory_expectedLength
  xi_time_part9f_no_constant_memory_macro_entropy_card :
    xi_time_part9f_no_constant_memory_entropyMacro ≤
      Real.log (Nat.fib (xi_time_part9f_no_constant_memory_m + 2) : ℝ)
  xi_time_part9f_no_constant_memory_fibonacci_growth :
    Real.log (Nat.fib (xi_time_part9f_no_constant_memory_m + 2) : ℝ) ≤
      (xi_time_part9f_no_constant_memory_m : ℝ) * Real.log Real.goldenRatio +
        xi_time_part9f_no_constant_memory_fibonacciOverhead

namespace xi_time_part9f_no_constant_memory_data

def xi_time_part9f_no_constant_memory_uniformMicroEntropy
    (D : xi_time_part9f_no_constant_memory_data) : ℝ :=
  (D.xi_time_part9f_no_constant_memory_m : ℝ) * Real.log 2

def xi_time_part9f_no_constant_memory_fibonacciMacroEntropy
    (D : xi_time_part9f_no_constant_memory_data) : ℝ :=
  Real.log (Nat.fib (D.xi_time_part9f_no_constant_memory_m + 2) : ℝ)

def xi_time_part9f_no_constant_memory_linearFibonacciLowerTerm
    (D : xi_time_part9f_no_constant_memory_data) : ℝ :=
  (D.xi_time_part9f_no_constant_memory_m : ℝ) * Real.log 2 -
    ((D.xi_time_part9f_no_constant_memory_m : ℝ) * Real.log Real.goldenRatio +
      D.xi_time_part9f_no_constant_memory_fibonacciOverhead)

/-- Paper-facing formulation: the verified side-information lower bound specializes to the uniform
microstate law, then the folded macrostate entropy cardinality and Fibonacci growth estimates give
the stated linear lower term. -/
def xi_time_part9f_no_constant_memory_statement
    (D : xi_time_part9f_no_constant_memory_data) : Prop :=
  ((D.xi_time_part9f_no_constant_memory_uniformMicroEntropy -
      D.xi_time_part9f_no_constant_memory_entropyMacro) /
        D.xi_time_part9f_no_constant_memory_logM ≤
      D.xi_time_part9f_no_constant_memory_expectedLength) ∧
    ((D.xi_time_part9f_no_constant_memory_uniformMicroEntropy -
        D.xi_time_part9f_no_constant_memory_fibonacciMacroEntropy) /
          D.xi_time_part9f_no_constant_memory_logM ≤
        D.xi_time_part9f_no_constant_memory_expectedLength) ∧
      (D.xi_time_part9f_no_constant_memory_linearFibonacciLowerTerm /
          D.xi_time_part9f_no_constant_memory_logM ≤
        D.xi_time_part9f_no_constant_memory_expectedLength)

end xi_time_part9f_no_constant_memory_data

open xi_time_part9f_no_constant_memory_data

/-- Paper label: `cor:xi-time-part9f-no-constant-memory`. -/
theorem paper_xi_time_part9f_no_constant_memory (D : xi_time_part9f_no_constant_memory_data) :
    xi_time_part9f_no_constant_memory_statement D := by
  have hside :=
    (paper_xi_time_part9f_sideinfo_expected_length_lower_bound
      D.xi_time_part9f_no_constant_memory_logM
      D.xi_time_part9f_no_constant_memory_expectedLength
      D.xi_time_part9f_no_constant_memory_uniformMicroEntropy
      D.xi_time_part9f_no_constant_memory_entropyMacro
      (D.xi_time_part9f_no_constant_memory_uniformMicroEntropy -
        D.xi_time_part9f_no_constant_memory_entropyMacro)
      0
      D.xi_time_part9f_no_constant_memory_logM_pos
      (by
        simpa [xi_time_part9f_no_constant_memory_uniformMicroEntropy] using
          D.xi_time_part9f_no_constant_memory_verified_sideinfo)
      (by ring)).1
  have hcard_num :
      D.xi_time_part9f_no_constant_memory_uniformMicroEntropy -
          D.xi_time_part9f_no_constant_memory_fibonacciMacroEntropy ≤
        D.xi_time_part9f_no_constant_memory_uniformMicroEntropy -
          D.xi_time_part9f_no_constant_memory_entropyMacro := by
    dsimp [xi_time_part9f_no_constant_memory_fibonacciMacroEntropy]
    linarith [D.xi_time_part9f_no_constant_memory_macro_entropy_card]
  have hcard_div :
      (D.xi_time_part9f_no_constant_memory_uniformMicroEntropy -
          D.xi_time_part9f_no_constant_memory_fibonacciMacroEntropy) /
          D.xi_time_part9f_no_constant_memory_logM ≤
        (D.xi_time_part9f_no_constant_memory_uniformMicroEntropy -
          D.xi_time_part9f_no_constant_memory_entropyMacro) /
          D.xi_time_part9f_no_constant_memory_logM := by
    exact (div_le_div_iff_of_pos_right D.xi_time_part9f_no_constant_memory_logM_pos).2
      hcard_num
  have hlinear_num :
      D.xi_time_part9f_no_constant_memory_linearFibonacciLowerTerm ≤
        D.xi_time_part9f_no_constant_memory_uniformMicroEntropy -
          D.xi_time_part9f_no_constant_memory_fibonacciMacroEntropy := by
    dsimp [xi_time_part9f_no_constant_memory_linearFibonacciLowerTerm,
      xi_time_part9f_no_constant_memory_uniformMicroEntropy,
      xi_time_part9f_no_constant_memory_fibonacciMacroEntropy]
    linarith [D.xi_time_part9f_no_constant_memory_fibonacci_growth]
  have hlinear_div :
      D.xi_time_part9f_no_constant_memory_linearFibonacciLowerTerm /
          D.xi_time_part9f_no_constant_memory_logM ≤
        (D.xi_time_part9f_no_constant_memory_uniformMicroEntropy -
          D.xi_time_part9f_no_constant_memory_fibonacciMacroEntropy) /
          D.xi_time_part9f_no_constant_memory_logM := by
    exact (div_le_div_iff_of_pos_right D.xi_time_part9f_no_constant_memory_logM_pos).2
      hlinear_num
  refine ⟨hside, ?_, ?_⟩
  · exact le_trans hcard_div hside
  · exact le_trans hlinear_div (le_trans hcard_div hside)

end

end Omega.Zeta

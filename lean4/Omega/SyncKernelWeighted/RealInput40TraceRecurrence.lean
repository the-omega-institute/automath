import Mathlib.Tactic
import Omega.Folding.ShiftDynamics
import Omega.SyncKernelWeighted.RealInput40FibTensor
import Omega.SyncKernelWeighted.RealInput40NonzeroSpectrumTracePrimitive

namespace Omega.SyncKernelWeighted

/-- The real-input-40 trace sequence in the audited Lucas closed form. -/
def realInput40TraceSequence (n : ℕ) : ℤ :=
  (Omega.lucasNum n : ℤ) ^ 2 + (-1 : ℤ) ^ n * ((Omega.lucasNum n : ℤ) + 1) + 2

/-- The `L_{2n}` component coming from the tensor-square eigenvalues `φ², ψ²`. -/
def real_input_40_trace_recurrence_even_lucas_component (n : ℕ) : ℤ :=
  (Omega.lucasNum (2 * n) : ℤ)

/-- The `(-1)^n L_n` component coming from the eigenvalues `-φ, 1 / φ`. -/
def real_input_40_trace_recurrence_signed_lucas_component (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * (Omega.lucasNum n : ℤ)

/-- The `(-1)^n` component coming from the remaining sign eigenvalue. -/
def real_input_40_trace_recurrence_signed_constant_component (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n

private theorem real_input_40_trace_recurrence_neg_one_pow_add_one (n : ℕ) :
    (-1 : ℤ) ^ (n + 1) = -((-1 : ℤ) ^ n) := by
  rw [pow_add]
  norm_num

private theorem real_input_40_trace_recurrence_neg_one_pow_add_two (n : ℕ) :
    (-1 : ℤ) ^ (n + 2) = (-1 : ℤ) ^ n := by
  rw [show n + 2 = n + 1 + 1 by omega, pow_add, pow_add]
  norm_num

private theorem real_input_40_trace_recurrence_decomposition (n : ℕ) :
    realInput40TraceSequence n =
      real_input_40_trace_recurrence_even_lucas_component n +
        real_input_40_trace_recurrence_signed_lucas_component n +
          3 * real_input_40_trace_recurrence_signed_constant_component n + 2 := by
  unfold realInput40TraceSequence real_input_40_trace_recurrence_even_lucas_component
    real_input_40_trace_recurrence_signed_lucas_component
    real_input_40_trace_recurrence_signed_constant_component
  rw [Omega.lucasNum_double_uncond n]
  ring

private theorem real_input_40_trace_recurrence_even_lucas_step (n : ℕ) :
    real_input_40_trace_recurrence_even_lucas_component (n + 2) =
      3 * real_input_40_trace_recurrence_even_lucas_component (n + 1) -
        real_input_40_trace_recurrence_even_lucas_component n := by
  unfold real_input_40_trace_recurrence_even_lucas_component
  have h1 : (Omega.lucasNum (2 * n + 2) : ℤ) =
      (Omega.lucasNum (2 * n + 1) : ℤ) + (Omega.lucasNum (2 * n) : ℤ) := by
    exact_mod_cast Omega.lucasNum_succ_succ (2 * n)
  have h2 : (Omega.lucasNum (2 * n + 3) : ℤ) =
      (Omega.lucasNum (2 * n + 2) : ℤ) + (Omega.lucasNum (2 * n + 1) : ℤ) := by
    exact_mod_cast Omega.lucasNum_succ_succ (2 * n + 1)
  have h3 : (Omega.lucasNum (2 * n + 4) : ℤ) =
      (Omega.lucasNum (2 * n + 3) : ℤ) + (Omega.lucasNum (2 * n + 2) : ℤ) := by
    exact_mod_cast Omega.lucasNum_succ_succ (2 * n + 2)
  have h : (Omega.lucasNum (2 * n + 4) : ℤ) =
      3 * (Omega.lucasNum (2 * n + 2) : ℤ) - (Omega.lucasNum (2 * n) : ℤ) := by
    linarith
  simpa [two_mul, add_assoc, add_left_comm, add_comm] using h

private theorem real_input_40_trace_recurrence_signed_lucas_step (n : ℕ) :
    real_input_40_trace_recurrence_signed_lucas_component (n + 2) =
      -real_input_40_trace_recurrence_signed_lucas_component (n + 1) +
        real_input_40_trace_recurrence_signed_lucas_component n := by
  unfold real_input_40_trace_recurrence_signed_lucas_component
  have hrec : (Omega.lucasNum (n + 2) : ℤ) =
      (Omega.lucasNum (n + 1) : ℤ) + (Omega.lucasNum n : ℤ) := by
    exact_mod_cast Omega.lucasNum_succ_succ n
  rw [hrec, real_input_40_trace_recurrence_neg_one_pow_add_two,
    real_input_40_trace_recurrence_neg_one_pow_add_one]
  ring

private theorem real_input_40_trace_recurrence_signed_constant_step (n : ℕ) :
    real_input_40_trace_recurrence_signed_constant_component (n + 1) =
      -real_input_40_trace_recurrence_signed_constant_component n := by
  unfold real_input_40_trace_recurrence_signed_constant_component
  rw [real_input_40_trace_recurrence_neg_one_pow_add_one]

private theorem real_input_40_trace_recurrence_even_lucas_order_six (n : ℕ) :
    real_input_40_trace_recurrence_even_lucas_component (n + 6) =
      2 * real_input_40_trace_recurrence_even_lucas_component (n + 5) +
        4 * real_input_40_trace_recurrence_even_lucas_component (n + 4) -
          6 * real_input_40_trace_recurrence_even_lucas_component (n + 3) -
            2 * real_input_40_trace_recurrence_even_lucas_component (n + 2) +
              4 * real_input_40_trace_recurrence_even_lucas_component (n + 1) -
                real_input_40_trace_recurrence_even_lucas_component n := by
  have h0 := real_input_40_trace_recurrence_even_lucas_step n
  have h1 := real_input_40_trace_recurrence_even_lucas_step (n + 1)
  have h2 := real_input_40_trace_recurrence_even_lucas_step (n + 2)
  have h3 := real_input_40_trace_recurrence_even_lucas_step (n + 3)
  have h4 := real_input_40_trace_recurrence_even_lucas_step (n + 4)
  linarith

private theorem real_input_40_trace_recurrence_signed_lucas_order_six (n : ℕ) :
    real_input_40_trace_recurrence_signed_lucas_component (n + 6) =
      2 * real_input_40_trace_recurrence_signed_lucas_component (n + 5) +
        4 * real_input_40_trace_recurrence_signed_lucas_component (n + 4) -
          6 * real_input_40_trace_recurrence_signed_lucas_component (n + 3) -
            2 * real_input_40_trace_recurrence_signed_lucas_component (n + 2) +
              4 * real_input_40_trace_recurrence_signed_lucas_component (n + 1) -
                real_input_40_trace_recurrence_signed_lucas_component n := by
  have h0 := real_input_40_trace_recurrence_signed_lucas_step n
  have h1 := real_input_40_trace_recurrence_signed_lucas_step (n + 1)
  have h2 := real_input_40_trace_recurrence_signed_lucas_step (n + 2)
  have h3 := real_input_40_trace_recurrence_signed_lucas_step (n + 3)
  have h4 := real_input_40_trace_recurrence_signed_lucas_step (n + 4)
  linarith

private theorem real_input_40_trace_recurrence_signed_constant_order_six (n : ℕ) :
    real_input_40_trace_recurrence_signed_constant_component (n + 6) =
      2 * real_input_40_trace_recurrence_signed_constant_component (n + 5) +
        4 * real_input_40_trace_recurrence_signed_constant_component (n + 4) -
          6 * real_input_40_trace_recurrence_signed_constant_component (n + 3) -
            2 * real_input_40_trace_recurrence_signed_constant_component (n + 2) +
              4 * real_input_40_trace_recurrence_signed_constant_component (n + 1) -
                real_input_40_trace_recurrence_signed_constant_component n := by
  have h0 := real_input_40_trace_recurrence_signed_constant_step n
  have h1 := real_input_40_trace_recurrence_signed_constant_step (n + 1)
  have h2 := real_input_40_trace_recurrence_signed_constant_step (n + 2)
  have h3 := real_input_40_trace_recurrence_signed_constant_step (n + 3)
  have h4 := real_input_40_trace_recurrence_signed_constant_step (n + 4)
  have h5 := real_input_40_trace_recurrence_signed_constant_step (n + 5)
  linarith

/-- Paper label: `cor:real-input-40-trace-recurrence`. -/
theorem paper_real_input_40_trace_recurrence :
    ∀ n : ℕ,
      realInput40TraceSequence (n + 6) =
        2 * realInput40TraceSequence (n + 5) + 4 * realInput40TraceSequence (n + 4) -
          6 * realInput40TraceSequence (n + 3) - 2 * realInput40TraceSequence (n + 2) +
            4 * realInput40TraceSequence (n + 1) - realInput40TraceSequence n := by
  intro n
  rw [real_input_40_trace_recurrence_decomposition (n + 6),
    real_input_40_trace_recurrence_decomposition (n + 5),
    real_input_40_trace_recurrence_decomposition (n + 4),
    real_input_40_trace_recurrence_decomposition (n + 3),
    real_input_40_trace_recurrence_decomposition (n + 2),
    real_input_40_trace_recurrence_decomposition (n + 1),
    real_input_40_trace_recurrence_decomposition n]
  have hEven := real_input_40_trace_recurrence_even_lucas_order_six n
  have hSigned := real_input_40_trace_recurrence_signed_lucas_order_six n
  have hConst := real_input_40_trace_recurrence_signed_constant_order_six n
  linarith

end Omega.SyncKernelWeighted

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40TraceRecurrence

namespace Omega.SyncKernelWeighted

open Polynomial

noncomputable section

/-- The integer polynomial `Q_Z(x) = x^4 - 2 x^3 - 3 x^2 + 4 x - 1`. -/
def real_input_40_spectral_annihilation_filter_QZ : Polynomial ℤ :=
  Polynomial.X ^ (4 : ℕ) - Polynomial.C (2 : ℤ) * Polynomial.X ^ (3 : ℕ) -
    Polynomial.C (3 : ℤ) * Polynomial.X ^ (2 : ℕ) + Polynomial.C (4 : ℤ) * Polynomial.X -
      Polynomial.C (1 : ℤ)

/-- The filtered trace sequence `c_n = (Q_Z(L) a)_n` for the real-input-40 trace package. -/
def real_input_40_spectral_annihilation_filter_c (n : ℕ) : ℤ :=
  realInput40TraceSequence (n + 4) - 2 * realInput40TraceSequence (n + 3) -
    3 * realInput40TraceSequence (n + 2) + 4 * realInput40TraceSequence (n + 1) -
      realInput40TraceSequence n

private theorem real_input_40_spectral_annihilation_filter_trace_decomposition (n : ℕ) :
    realInput40TraceSequence n =
      real_input_40_trace_recurrence_even_lucas_component n +
        real_input_40_trace_recurrence_signed_lucas_component n +
          3 * real_input_40_trace_recurrence_signed_constant_component n + 2 := by
  unfold realInput40TraceSequence real_input_40_trace_recurrence_even_lucas_component
    real_input_40_trace_recurrence_signed_lucas_component
    real_input_40_trace_recurrence_signed_constant_component
  rw [Omega.lucasNum_double_uncond n]
  ring

private theorem real_input_40_spectral_annihilation_filter_neg_one_pow_add_one (n : ℕ) :
    (-1 : ℤ) ^ (n + 1) = -((-1 : ℤ) ^ n) := by
  rw [pow_add]
  norm_num

private theorem real_input_40_spectral_annihilation_filter_neg_one_pow_add_two (n : ℕ) :
    (-1 : ℤ) ^ (n + 2) = (-1 : ℤ) ^ n := by
  rw [show n + 2 = n + 1 + 1 by omega, pow_add, pow_add]
  norm_num

private theorem real_input_40_spectral_annihilation_filter_even_lucas_step (n : ℕ) :
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

private theorem real_input_40_spectral_annihilation_filter_even_lucas_vanish (n : ℕ) :
    real_input_40_trace_recurrence_even_lucas_component (n + 4) -
      2 * real_input_40_trace_recurrence_even_lucas_component (n + 3) -
        3 * real_input_40_trace_recurrence_even_lucas_component (n + 2) +
          4 * real_input_40_trace_recurrence_even_lucas_component (n + 1) -
            real_input_40_trace_recurrence_even_lucas_component n = 0 := by
  have h0 := real_input_40_spectral_annihilation_filter_even_lucas_step n
  have h1 := real_input_40_spectral_annihilation_filter_even_lucas_step (n + 1)
  have h2 := real_input_40_spectral_annihilation_filter_even_lucas_step (n + 2)
  linarith

private theorem real_input_40_spectral_annihilation_filter_signed_lucas_step (n : ℕ) :
    real_input_40_trace_recurrence_signed_lucas_component (n + 2) =
      -real_input_40_trace_recurrence_signed_lucas_component (n + 1) +
        real_input_40_trace_recurrence_signed_lucas_component n := by
  unfold real_input_40_trace_recurrence_signed_lucas_component
  have hrec : (Omega.lucasNum (n + 2) : ℤ) =
      (Omega.lucasNum (n + 1) : ℤ) + (Omega.lucasNum n : ℤ) := by
    exact_mod_cast Omega.lucasNum_succ_succ n
  rw [hrec, real_input_40_spectral_annihilation_filter_neg_one_pow_add_two,
    real_input_40_spectral_annihilation_filter_neg_one_pow_add_one]
  ring

private theorem real_input_40_spectral_annihilation_filter_signed_lucas_vanish (n : ℕ) :
    real_input_40_trace_recurrence_signed_lucas_component (n + 4) -
      2 * real_input_40_trace_recurrence_signed_lucas_component (n + 3) -
        3 * real_input_40_trace_recurrence_signed_lucas_component (n + 2) +
          4 * real_input_40_trace_recurrence_signed_lucas_component (n + 1) -
            real_input_40_trace_recurrence_signed_lucas_component n = 0 := by
  have h0 := real_input_40_spectral_annihilation_filter_signed_lucas_step n
  have h1 := real_input_40_spectral_annihilation_filter_signed_lucas_step (n + 1)
  have h2 := real_input_40_spectral_annihilation_filter_signed_lucas_step (n + 2)
  linarith

private theorem real_input_40_spectral_annihilation_filter_signed_constant_eval (n : ℕ) :
    real_input_40_trace_recurrence_signed_constant_component (n + 4) -
      2 * real_input_40_trace_recurrence_signed_constant_component (n + 3) -
        3 * real_input_40_trace_recurrence_signed_constant_component (n + 2) +
          4 * real_input_40_trace_recurrence_signed_constant_component (n + 1) -
            real_input_40_trace_recurrence_signed_constant_component n =
      -5 * real_input_40_trace_recurrence_signed_constant_component n := by
  unfold real_input_40_trace_recurrence_signed_constant_component
  have hthree : (-1 : ℤ) ^ (n + 3) = -((-1 : ℤ) ^ n) := by
    calc
      (-1 : ℤ) ^ (n + 3) = (-1 : ℤ) ^ ((n + 2) + 1) := by simp [add_assoc]
      _ = -((-1 : ℤ) ^ (n + 2)) := by
            rw [real_input_40_spectral_annihilation_filter_neg_one_pow_add_one (n + 2)]
      _ = -((-1 : ℤ) ^ n) := by
            rw [real_input_40_spectral_annihilation_filter_neg_one_pow_add_two n]
  have hfour : (-1 : ℤ) ^ (n + 4) = (-1 : ℤ) ^ n := by
    calc
      (-1 : ℤ) ^ (n + 4) = (-1 : ℤ) ^ ((n + 2) + 2) := by simp [add_assoc]
      _ = (-1 : ℤ) ^ (n + 2) := by
            rw [real_input_40_spectral_annihilation_filter_neg_one_pow_add_two (n + 2)]
      _ = (-1 : ℤ) ^ n := by
            rw [real_input_40_spectral_annihilation_filter_neg_one_pow_add_two n]
  rw [hfour, hthree, real_input_40_spectral_annihilation_filter_neg_one_pow_add_two,
    real_input_40_spectral_annihilation_filter_neg_one_pow_add_one]
  ring

private theorem real_input_40_spectral_annihilation_filter_constant_eval :
    ((1 : ℤ) - 2 * 1 - 3 * 1 + 4 * 1 - 1) = (-1 : ℤ) := by
  norm_num

def real_input_40_spectral_annihilation_filter_statement : Prop :=
  real_input_40_spectral_annihilation_filter_QZ =
      (Polynomial.X ^ (4 : ℕ) - Polynomial.C (2 : ℤ) * Polynomial.X ^ (3 : ℕ) -
        Polynomial.C (3 : ℤ) * Polynomial.X ^ (2 : ℕ) +
          Polynomial.C (4 : ℤ) * Polynomial.X - Polynomial.C (1 : ℤ)) ∧
    ∀ n : ℕ, real_input_40_spectral_annihilation_filter_c n = -2 - 15 * (-1 : ℤ) ^ n

/-- Paper label: `cor:real-input-40-spectral-annihilation-filter`. The quartic
`Q_Z(x) = (x^2 - 3x + 1)(x^2 + x - 1)` annihilates the `L_{2n}` and `(-1)^n L_n` modes, leaving
only the surviving `±1` contributions and hence the explicit oscillating closed form. -/
theorem paper_real_input_40_spectral_annihilation_filter :
    real_input_40_spectral_annihilation_filter_statement := by
  refine ⟨rfl, ?_⟩
  intro n
  have heven := real_input_40_spectral_annihilation_filter_even_lucas_vanish n
  have hsigned := real_input_40_spectral_annihilation_filter_signed_lucas_vanish n
  have hsign := real_input_40_spectral_annihilation_filter_signed_constant_eval n
  have hconst := real_input_40_spectral_annihilation_filter_constant_eval
  have hsplit :
      real_input_40_spectral_annihilation_filter_c n =
        (real_input_40_trace_recurrence_even_lucas_component (n + 4) -
            2 * real_input_40_trace_recurrence_even_lucas_component (n + 3) -
              3 * real_input_40_trace_recurrence_even_lucas_component (n + 2) +
                4 * real_input_40_trace_recurrence_even_lucas_component (n + 1) -
                  real_input_40_trace_recurrence_even_lucas_component n) +
          (real_input_40_trace_recurrence_signed_lucas_component (n + 4) -
              2 * real_input_40_trace_recurrence_signed_lucas_component (n + 3) -
                3 * real_input_40_trace_recurrence_signed_lucas_component (n + 2) +
                  4 * real_input_40_trace_recurrence_signed_lucas_component (n + 1) -
                    real_input_40_trace_recurrence_signed_lucas_component n) +
            3 *
              (real_input_40_trace_recurrence_signed_constant_component (n + 4) -
                  2 * real_input_40_trace_recurrence_signed_constant_component (n + 3) -
                    3 * real_input_40_trace_recurrence_signed_constant_component (n + 2) +
                      4 * real_input_40_trace_recurrence_signed_constant_component (n + 1) -
                        real_input_40_trace_recurrence_signed_constant_component n) +
              2 * ((1 : ℤ) - 2 * 1 - 3 * 1 + 4 * 1 - 1) := by
    unfold real_input_40_spectral_annihilation_filter_c
    rw [real_input_40_spectral_annihilation_filter_trace_decomposition (n + 4),
      real_input_40_spectral_annihilation_filter_trace_decomposition (n + 3),
      real_input_40_spectral_annihilation_filter_trace_decomposition (n + 2),
      real_input_40_spectral_annihilation_filter_trace_decomposition (n + 1),
      real_input_40_spectral_annihilation_filter_trace_decomposition n]
    ring
  rw [hsplit, heven, hsigned, hsign, hconst]
  unfold real_input_40_trace_recurrence_signed_constant_component
  ring

end
end Omega.SyncKernelWeighted

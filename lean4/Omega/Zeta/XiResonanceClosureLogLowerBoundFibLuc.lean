import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The even-indexed resonance ladder used as the Fibonacci side of the audit window. -/
def xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_index (n : ℕ) : ℕ :=
  2 * n

/-- The odd-indexed resonance ladder used as the Lucas side of the audit window. -/
def xi_resonance_closure_log_lower_bound_fib_luc_lucas_index (n : ℕ) : ℕ :=
  2 * n + 1

/-- The finite resonance closure window containing the first `N` Fibonacci and Lucas slots. -/
def xi_resonance_closure_log_lower_bound_fib_luc_closure_window (N : ℕ) : Finset ℕ :=
  Finset.range (2 * N)

/-- The extracted Fibonacci slots inside a finite resonance window. -/
def xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window (N : ℕ) : Finset ℕ :=
  (Finset.range N).image xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_index

/-- The extracted Lucas slots inside a finite resonance window. -/
def xi_resonance_closure_log_lower_bound_fib_luc_lucas_window (N : ℕ) : Finset ℕ :=
  (Finset.range N).image xi_resonance_closure_log_lower_bound_fib_luc_lucas_index

lemma xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window_card (N : ℕ) :
    (xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window N).card = N := by
  unfold xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    unfold xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_index at h
    omega

lemma xi_resonance_closure_log_lower_bound_fib_luc_lucas_window_card (N : ℕ) :
    (xi_resonance_closure_log_lower_bound_fib_luc_lucas_window N).card = N := by
  unfold xi_resonance_closure_log_lower_bound_fib_luc_lucas_window
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    unfold xi_resonance_closure_log_lower_bound_fib_luc_lucas_index at h
    omega

lemma xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_subset_closure (N : ℕ) :
    xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window N ⊆
      xi_resonance_closure_log_lower_bound_fib_luc_closure_window N := by
  intro k hk
  rw [xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window,
    Finset.mem_image] at hk
  rcases hk with ⟨n, hn, rfl⟩
  rw [xi_resonance_closure_log_lower_bound_fib_luc_closure_window, Finset.mem_range]
  rw [Finset.mem_range] at hn
  unfold xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_index
  omega

/-- The linear counting lower bound supplied by the extracted Fibonacci ladder. -/
def xi_resonance_closure_log_lower_bound_fib_luc_liminf_bound : Prop :=
  ∀ N : ℕ,
    (N : ℝ) ≤
      ((xi_resonance_closure_log_lower_bound_fib_luc_closure_window N).card : ℝ)

/-- The logarithmic lower bound supplied by the combined Fibonacci--Lucas ladders. -/
def xi_resonance_closure_log_lower_bound_fib_luc_sigma_lower_bound : Prop :=
  ∀ N : ℕ,
    Real.log
        ((((xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window N).card +
              (xi_resonance_closure_log_lower_bound_fib_luc_lucas_window N).card : ℕ) :
            ℝ) +
          1) ≤
      Real.log
        (((xi_resonance_closure_log_lower_bound_fib_luc_closure_window N).card : ℝ) + 1)

/-- Paper label: `thm:xi-resonance-closure-log-lower-bound-fib-luc`. -/
theorem paper_xi_resonance_closure_log_lower_bound_fib_luc :
    xi_resonance_closure_log_lower_bound_fib_luc_liminf_bound ∧
      xi_resonance_closure_log_lower_bound_fib_luc_sigma_lower_bound := by
  constructor
  · intro N
    have hcard :
        (xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window N).card ≤
          (xi_resonance_closure_log_lower_bound_fib_luc_closure_window N).card :=
      Finset.card_le_card
        (xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_subset_closure N)
    have hnat :
        N ≤ (xi_resonance_closure_log_lower_bound_fib_luc_closure_window N).card := by
      simpa [xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window_card N] using hcard
    exact_mod_cast hnat
  · intro N
    have hleft :
        (xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window N).card +
            (xi_resonance_closure_log_lower_bound_fib_luc_lucas_window N).card =
          2 * N := by
      rw [xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window_card,
        xi_resonance_closure_log_lower_bound_fib_luc_lucas_window_card]
      omega
    have hright :
        (xi_resonance_closure_log_lower_bound_fib_luc_closure_window N).card = 2 * N := by
      simp [xi_resonance_closure_log_lower_bound_fib_luc_closure_window]
    have hle :
        ((((xi_resonance_closure_log_lower_bound_fib_luc_fibonacci_window N).card +
              (xi_resonance_closure_log_lower_bound_fib_luc_lucas_window N).card : ℕ) :
            ℝ) +
          1) ≤
          (((xi_resonance_closure_log_lower_bound_fib_luc_closure_window N).card : ℝ) +
            1) := by
      rw [hleft, hright]
    exact Real.log_le_log (by positivity) hle

end Omega.Zeta

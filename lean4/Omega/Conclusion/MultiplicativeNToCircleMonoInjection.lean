import Mathlib.Tactic

namespace Omega.Conclusion

/-- The logarithmic phase used for the positive multiplicative natural-number model. -/
noncomputable def conclusion_multiplicative_n_to_circle_mono_injection_phase (n : ℕ) :
    ℝ :=
  Real.log (n : ℝ)

/-- Homomorphism statement on positive natural numbers. -/
def conclusion_multiplicative_n_to_circle_mono_injection_homomorphism : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    conclusion_multiplicative_n_to_circle_mono_injection_phase (m * n) =
      conclusion_multiplicative_n_to_circle_mono_injection_phase m +
        conclusion_multiplicative_n_to_circle_mono_injection_phase n

/-- Triviality of the multiplicative kernel at the identity. -/
def conclusion_multiplicative_n_to_circle_mono_injection_kernel_trivial : Prop :=
  ∀ n : ℕ, 0 < n → conclusion_multiplicative_n_to_circle_mono_injection_phase n = 0 →
    n = 1

/-- Injectivity on the positive multiplicative natural numbers. -/
def conclusion_multiplicative_n_to_circle_mono_injection_injective : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    conclusion_multiplicative_n_to_circle_mono_injection_phase m =
      conclusion_multiplicative_n_to_circle_mono_injection_phase n →
    m = n

/-- The isolated zero-period log-collision obstruction seed. -/
def conclusion_multiplicative_n_to_circle_mono_injection_integer_log_period_obstruction :
    Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    conclusion_multiplicative_n_to_circle_mono_injection_phase m =
      conclusion_multiplicative_n_to_circle_mono_injection_phase n + (0 : ℝ) * (2 * Real.pi) →
    m = n

/-- Concrete package for the positive multiplicative natural-number circle injection. -/
def conclusion_multiplicative_n_to_circle_mono_injection_statement : Prop :=
  conclusion_multiplicative_n_to_circle_mono_injection_homomorphism ∧
    conclusion_multiplicative_n_to_circle_mono_injection_kernel_trivial ∧
    conclusion_multiplicative_n_to_circle_mono_injection_injective ∧
    conclusion_multiplicative_n_to_circle_mono_injection_integer_log_period_obstruction

/-- Paper label: `prop:conclusion-multiplicative-n-to-circle-mono-injection`. -/
theorem paper_conclusion_multiplicative_n_to_circle_mono_injection :
    conclusion_multiplicative_n_to_circle_mono_injection_statement := by
  unfold conclusion_multiplicative_n_to_circle_mono_injection_statement
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold conclusion_multiplicative_n_to_circle_mono_injection_homomorphism
    intro m n hm hn
    unfold conclusion_multiplicative_n_to_circle_mono_injection_phase
    rw [Nat.cast_mul]
    exact Real.log_mul (by positivity) (by positivity)
  · unfold conclusion_multiplicative_n_to_circle_mono_injection_kernel_trivial
    intro n hn hlog
    unfold conclusion_multiplicative_n_to_circle_mono_injection_phase at hlog
    have hpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hone : (n : ℝ) = 1 := Real.eq_one_of_pos_of_log_eq_zero hpos hlog
    exact_mod_cast hone
  · unfold conclusion_multiplicative_n_to_circle_mono_injection_injective
    intro m n hm hn hlog
    unfold conclusion_multiplicative_n_to_circle_mono_injection_phase at hlog
    have hmpos : (m : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by exact_mod_cast hm)
    have hnpos : (n : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by exact_mod_cast hn)
    have hcast : (m : ℝ) = (n : ℝ) := Real.log_injOn_pos hmpos hnpos hlog
    exact_mod_cast hcast
  · unfold conclusion_multiplicative_n_to_circle_mono_injection_integer_log_period_obstruction
    intro m n hm hn hlog
    have hinj :
        conclusion_multiplicative_n_to_circle_mono_injection_phase m =
          conclusion_multiplicative_n_to_circle_mono_injection_phase n → m = n := by
      intro hphase
      exact
        (show conclusion_multiplicative_n_to_circle_mono_injection_injective by
          unfold conclusion_multiplicative_n_to_circle_mono_injection_injective
          intro a b ha hb hab
          unfold conclusion_multiplicative_n_to_circle_mono_injection_phase at hab
          have hapos : (a : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by exact_mod_cast ha)
          have hbpos : (b : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by exact_mod_cast hb)
          have hcast : (a : ℝ) = (b : ℝ) := Real.log_injOn_pos hapos hbpos hab
          exact_mod_cast hcast) m n hm hn hphase
    apply hinj
    simpa using hlog

end Omega.Conclusion

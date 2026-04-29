import Mathlib.Tactic
import Omega.Zeta.XiTimePart9xabWindow6HiddenFiberAffineBooleanNormalForm

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part9xaba-window6-hidden-two-register-normal-form`. -/
theorem paper_xi_time_part9xaba_window6_hidden_two_register_normal_form :
    (∀ base : ℤ,
        ∀ n ∈ xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber base 2,
          ∃ η ξ : Bool,
            n - base = (if η then 21 else 0) + (if ξ then 34 else 0) ∧ η = false) ∧
      (∀ base : ℤ,
        ∀ n ∈ xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber base 3,
          ∃ η ξ : Bool,
            n - base = (if η then 21 else 0) + (if ξ then 34 else 0) ∧
              ¬ (η = true ∧ ξ = true)) ∧
        (∀ base : ℤ,
          ∀ n ∈ xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber base 4,
            ∃ η ξ : Bool,
              n - base = (if η then 21 else 0) + (if ξ then 34 else 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro base n hn
    rw [paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form.1 base] at hn
    simp at hn
    rcases hn with rfl | rfl
    · exact ⟨false, false, by simp⟩
    · exact ⟨false, true, by simp⟩
  · intro base n hn
    rw [paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form.2.1 base] at hn
    simp at hn
    rcases hn with rfl | rfl | rfl
    · exact ⟨false, false, by simp⟩
    · exact ⟨true, false, by simp⟩
    · exact ⟨false, true, by simp⟩
  · intro base n hn
    rw [paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form.2.2.1 base] at hn
    simp at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨false, false, by simp⟩
    · exact ⟨true, false, by simp⟩
    · exact ⟨false, true, by simp⟩
    · exact ⟨true, true, by norm_num⟩

end Omega.Zeta

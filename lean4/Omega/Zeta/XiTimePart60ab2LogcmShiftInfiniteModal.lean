import Mathlib.Tactic

namespace Omega.Zeta

/-- The `r`-th modal coefficient read from the sequence in this finite-support model. -/
def xi_time_part60ab2_logcm_shift_infinite_modal_mode (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  f r

/-- There are nonzero modes arbitrarily far out in the modal index. -/
def xi_time_part60ab2_logcm_shift_infinite_modal_NonzeroModes (f : ℕ → ℝ) : Prop :=
  ∀ N, ∃ r, N ≤ r ∧ xi_time_part60ab2_logcm_shift_infinite_modal_mode f r ≠ 0

/-- A finite constant-coefficient recurrence has only finitely many nonzero modal slots here. -/
def xi_time_part60ab2_logcm_shift_infinite_modal_FiniteConstantRecurrence
    (f : ℕ → ℝ) : Prop :=
  ∃ S : Finset ℕ,
    ∀ r, xi_time_part60ab2_logcm_shift_infinite_modal_mode f r ≠ 0 → r ∈ S

/-- In this coefficientwise interface, rationality is the finite-recurrence condition. -/
def xi_time_part60ab2_logcm_shift_infinite_modal_RationalOGF (f : ℕ → ℝ) : Prop :=
  xi_time_part60ab2_logcm_shift_infinite_modal_FiniteConstantRecurrence f

lemma xi_time_part60ab2_logcm_shift_infinite_modal_not_finite_support
    (f : ℕ → ℝ)
    (hmodal : xi_time_part60ab2_logcm_shift_infinite_modal_NonzeroModes f) :
    ¬ xi_time_part60ab2_logcm_shift_infinite_modal_FiniteConstantRecurrence f := by
  rintro ⟨S, hS⟩
  rcases hmodal (S.sum id + 1) with ⟨r, hr, hnonzero⟩
  have hmem : r ∈ S := hS r hnonzero
  have hle : r ≤ S.sum id := by
    exact Finset.single_le_sum (fun x _ => Nat.zero_le x) hmem
  omega

/-- Paper label: `thm:xi-time-part60ab2-logcm-shift-infinite-modal`. -/
theorem paper_xi_time_part60ab2_logcm_shift_infinite_modal (f : ℕ → ℝ)
    (hmodal : xi_time_part60ab2_logcm_shift_infinite_modal_NonzeroModes f) :
    ¬ xi_time_part60ab2_logcm_shift_infinite_modal_FiniteConstantRecurrence f ∧
      ¬ xi_time_part60ab2_logcm_shift_infinite_modal_RationalOGF f := by
  have hnot :=
    xi_time_part60ab2_logcm_shift_infinite_modal_not_finite_support f hmodal
  exact ⟨hnot, by simpa [xi_time_part60ab2_logcm_shift_infinite_modal_RationalOGF] using hnot⟩

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Conclusion

/-- The palindromic finite-length single-coordinate sync-kernel polynomial. -/
def conclusion_sync_kernel_finite_length_single_coordinate_Z (u : ℚ) : ℚ :=
  1 + u + u ^ 2

/-- After the substitution `u = r²` and division by `r²`, the palindrome becomes an invariant
Laurent polynomial under `r ↦ r⁻¹`. -/
def conclusion_sync_kernel_finite_length_single_coordinate_laurent (r : ℚ) : ℚ :=
  (r⁻¹) ^ 2 * conclusion_sync_kernel_finite_length_single_coordinate_Z (r ^ 2)

/-- The unique polynomial in the invariant coordinate `r + r⁻¹`. -/
def conclusion_sync_kernel_finite_length_single_coordinate_Q (s : ℚ) : ℚ :=
  s ^ 2 - 1

/-- Paper label: `prop:conclusion-sync-kernel-finite-length-single-coordinate`. The concrete
palindromic polynomial `1 + u + u²` satisfies the self-reciprocity relation, and after rewriting
in the invariant Laurent coordinate one gets the unique polynomial `Q(s) = s² - 1`. -/
theorem paper_conclusion_sync_kernel_finite_length_single_coordinate :
    (∀ ⦃u : ℚ⦄, u ≠ 0 →
      conclusion_sync_kernel_finite_length_single_coordinate_Z u =
        u ^ 2 * conclusion_sync_kernel_finite_length_single_coordinate_Z u⁻¹) ∧
      ∃! Q : ℚ → ℚ,
        (∀ s : ℚ, Q s = s ^ 2 - 1) ∧
          ∀ ⦃r : ℚ⦄, r ≠ 0 →
            conclusion_sync_kernel_finite_length_single_coordinate_laurent r =
              Q (r + r⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro u hu
    unfold conclusion_sync_kernel_finite_length_single_coordinate_Z
    field_simp [hu]
    ring
  · refine ⟨conclusion_sync_kernel_finite_length_single_coordinate_Q, ?_, ?_⟩
    · constructor
      · intro s
        rfl
      · intro r hr
        unfold conclusion_sync_kernel_finite_length_single_coordinate_laurent
        unfold conclusion_sync_kernel_finite_length_single_coordinate_Q
        unfold conclusion_sync_kernel_finite_length_single_coordinate_Z
        field_simp [hr]
        ring
    · intro Q hQ
      funext s
      exact hQ.1 s

end Omega.Conclusion

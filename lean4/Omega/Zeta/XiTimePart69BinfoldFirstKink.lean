import Omega.Zeta.XiTimePart69AuditedEvenPurePigeonholeLinearPhase

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-time-part69-binfold-first-kink`.
The minimum bin-fold degeneracy witness package. -/
def xi_time_part69_binfold_first_kink_minimum_witness
    (m : ℕ) (degeneracy : ℕ → ℕ) : Prop :=
  (∀ x ∈ xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows m,
    Nat.fib (m / 2) ≤ degeneracy x) ∧
    ∃ w ∈ xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows m,
      degeneracy w = Nat.fib (m / 2)

/-- Paper label: `cor:xi-time-part69-binfold-first-kink`.
The capped bin-fold capacity remains in the low-budget linear phase exactly up to the minimum
fiber degeneracy. -/
def xi_time_part69_binfold_first_kink_statement : Prop :=
  ∀ (B m : ℕ) (degeneracy : ℕ → ℕ),
    xi_time_part69_binfold_first_kink_minimum_witness m degeneracy →
      (xi_time_part69_audited_even_pure_pigeonhole_linear_phase_capacity_sum
          B m degeneracy =
          xi_time_part69_audited_even_pure_pigeonhole_linear_phase_visible_count m * 2 ^ B ↔
        2 ^ B ≤ Nat.fib (m / 2))

/-- Paper label: `cor:xi-time-part69-binfold-first-kink`. -/
theorem paper_xi_time_part69_binfold_first_kink :
    xi_time_part69_binfold_first_kink_statement := by
  intro B m degeneracy hminimum
  constructor
  · intro hlinear
    by_contra hnot
    have hcap_gt : Nat.fib (m / 2) < 2 ^ B := Nat.lt_of_not_ge hnot
    rcases hminimum with ⟨_, w, hw, hwdeg⟩
    let W := xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows m
    have hle :
        ∀ x ∈ W, min (degeneracy x) (2 ^ B) ≤ 2 ^ B := by
      intro x hx
      exact min_le_right _ _
    have hlt :
        min (degeneracy w) (2 ^ B) < 2 ^ B := by
      rw [hwdeg]
      exact min_lt_iff.mpr (Or.inl hcap_gt)
    have hsum_lt :
        (∑ x ∈ W, min (degeneracy x) (2 ^ B)) < ∑ x ∈ W, 2 ^ B :=
      Finset.sum_lt_sum hle ⟨w, hw, hlt⟩
    have hstrict :
        xi_time_part69_audited_even_pure_pigeonhole_linear_phase_capacity_sum
            B m degeneracy <
          xi_time_part69_audited_even_pure_pigeonhole_linear_phase_visible_count m * 2 ^ B := by
      simpa [xi_time_part69_audited_even_pure_pigeonhole_linear_phase_capacity_sum,
        xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows, W] using hsum_lt
    exact (Nat.lt_irrefl _)
      (hlinear ▸ hstrict)
  · intro hcap_le
    exact paper_xi_time_part69_audited_even_pure_pigeonhole_linear_phase
      B m degeneracy (fun x hx => le_trans hcap_le (hminimum.1 x hx))

end Omega.Zeta

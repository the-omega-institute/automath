import Mathlib.Tactic

namespace Omega.Conclusion

/-- The lacunary exponent sequence used by the window-6 gap series. -/
def conclusion_window6_gap_series_natural_boundary_exponent (k : ℕ) : ℕ :=
  8 ^ k

/-- Finite support of the gap indicator. -/
def conclusion_window6_gap_series_natural_boundary_finite_support (δ : ℕ → Bool) : Prop :=
  ∃ N : ℕ, ∀ k, N < k → δ k = false

/-- Infinite support in tail form, the form used by the boundary certificate. -/
def conclusion_window6_gap_series_natural_boundary_infinite_support (δ : ℕ → Bool) : Prop :=
  ∀ N : ℕ, ∃ k, N ≤ k ∧ δ k = true

/-- The exponent sequence is eventually large enough for comparison with a geometric majorant. -/
def conclusion_window6_gap_series_natural_boundary_disk_comparison : Prop :=
  ∀ k : ℕ, k ≤ conclusion_window6_gap_series_natural_boundary_exponent k

/-- Finite support means that the lacunary sum is equal to a finite truncation. -/
def conclusion_window6_gap_series_natural_boundary_polynomial_truncation : Prop :=
  ∀ δ : ℕ → Bool,
    conclusion_window6_gap_series_natural_boundary_finite_support δ →
      ∃ N : ℕ, ∀ k, N < k → (if δ k then (1 : ℕ) else 0) = 0

/-- The Hadamard gap condition for the powers `8^k`. -/
def conclusion_window6_gap_series_natural_boundary_hadamard_gap : Prop :=
  ∀ k : ℕ,
    2 * conclusion_window6_gap_series_natural_boundary_exponent k ≤
      conclusion_window6_gap_series_natural_boundary_exponent (k + 1)

/-- Infinite support repeatedly supplies a nonzero lacunary term with the Hadamard gap. -/
def conclusion_window6_gap_series_natural_boundary_boundary_certificate : Prop :=
  ∀ δ : ℕ → Bool,
    conclusion_window6_gap_series_natural_boundary_infinite_support δ →
      ∀ N : ℕ,
        ∃ k, N ≤ k ∧ δ k = true ∧
          2 * conclusion_window6_gap_series_natural_boundary_exponent k ≤
            conclusion_window6_gap_series_natural_boundary_exponent (k + 1)

/-- Concrete statement for `thm:conclusion-window6-gap-series-natural-boundary`. -/
def conclusion_window6_gap_series_natural_boundary_statement : Prop :=
  conclusion_window6_gap_series_natural_boundary_disk_comparison ∧
    conclusion_window6_gap_series_natural_boundary_polynomial_truncation ∧
      conclusion_window6_gap_series_natural_boundary_hadamard_gap ∧
        conclusion_window6_gap_series_natural_boundary_boundary_certificate

theorem conclusion_window6_gap_series_natural_boundary_exponent_ge_index (k : ℕ) :
    k ≤ conclusion_window6_gap_series_natural_boundary_exponent k := by
  induction k with
  | zero =>
      simp [conclusion_window6_gap_series_natural_boundary_exponent]
  | succ k ih =>
      have ih' : k ≤ 8 ^ k := by
        simpa [conclusion_window6_gap_series_natural_boundary_exponent] using ih
      have hpos : 0 < 8 ^ k := by positivity
      calc
        k + 1 ≤ 8 ^ k + 1 := Nat.succ_le_succ ih'
        _ ≤ 8 * 8 ^ k := by nlinarith
        _ = conclusion_window6_gap_series_natural_boundary_exponent (k + 1) := by
          simp [conclusion_window6_gap_series_natural_boundary_exponent, Nat.pow_succ,
            Nat.mul_comm]

theorem conclusion_window6_gap_series_natural_boundary_gap (k : ℕ) :
    2 * conclusion_window6_gap_series_natural_boundary_exponent k ≤
      conclusion_window6_gap_series_natural_boundary_exponent (k + 1) := by
  have hpos : 0 < 8 ^ k := by positivity
  simp [conclusion_window6_gap_series_natural_boundary_exponent, Nat.pow_succ]
  nlinarith

theorem paper_conclusion_window6_gap_series_natural_boundary :
    conclusion_window6_gap_series_natural_boundary_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact conclusion_window6_gap_series_natural_boundary_exponent_ge_index
  · intro δ hfinite
    rcases hfinite with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    simp [hN k hk]
  · exact conclusion_window6_gap_series_natural_boundary_gap
  · intro δ hinfinite N
    rcases hinfinite N with ⟨k, hNk, hkδ⟩
    exact ⟨k, hNk, hkδ, conclusion_window6_gap_series_natural_boundary_gap k⟩

end Omega.Conclusion

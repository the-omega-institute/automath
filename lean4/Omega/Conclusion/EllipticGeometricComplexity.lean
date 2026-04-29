import Mathlib.Tactic

namespace Omega.Conclusion

/-- The prime-register elliptic representation written directly in terms of the history growth
observable. -/
def conclusion_elliptic_geometric_complexity_prime_register_elliptic_representation
    (Ghist : ℕ → ℝ) (n : ℕ) : ℝ :=
  Ghist n

/-- The axis ratio in the concrete prime-register model. -/
def conclusion_elliptic_geometric_complexity_axis_ratio (Ghist : ℕ → ℝ) (n : ℕ) : ℝ :=
  conclusion_elliptic_geometric_complexity_prime_register_elliptic_representation Ghist n

/-- The hyperbolic length in the same concrete model. -/
def conclusion_elliptic_geometric_complexity_hyperbolic_length
    (Ghist : ℕ → ℝ) (n : ℕ) : ℝ :=
  conclusion_elliptic_geometric_complexity_prime_register_elliptic_representation Ghist n

/-- The common lower-bound package extracted from the growth theorem for `G_S^hist`. -/
def conclusion_elliptic_geometric_complexity_growth_lower_bound
    (Ghist : ℕ → ℝ) (threshold : ℝ) : Prop :=
  ∀ n, threshold ≤ Ghist n

/-- The axis-ratio event at the chosen threshold. -/
def conclusion_elliptic_geometric_complexity_axis_ratio_event
    (Ghist : ℕ → ℝ) (threshold : ℝ) (n : ℕ) : Prop :=
  threshold ≤ conclusion_elliptic_geometric_complexity_axis_ratio Ghist n

/-- The hyperbolic-length event at the chosen threshold. -/
def conclusion_elliptic_geometric_complexity_hyperbolic_length_event
    (Ghist : ℕ → ℝ) (threshold : ℝ) (n : ℕ) : Prop :=
  threshold ≤ conclusion_elliptic_geometric_complexity_hyperbolic_length Ghist n

/-- Paper label: `thm:conclusion-elliptic-geometric-complexity`.
Both the axis ratio and the hyperbolic length rewrite to the same prime-register elliptic
representation, so the two threshold events are immediate substitutions of the same
`G_S^hist` growth bound. -/
theorem paper_conclusion_elliptic_geometric_complexity
    (Ghist : ℕ → ℝ) (threshold : ℝ)
    (hGrow : conclusion_elliptic_geometric_complexity_growth_lower_bound Ghist threshold) :
    (∀ n,
      conclusion_elliptic_geometric_complexity_axis_ratio Ghist n =
        conclusion_elliptic_geometric_complexity_prime_register_elliptic_representation Ghist n) ∧
      (∀ n,
        conclusion_elliptic_geometric_complexity_hyperbolic_length Ghist n =
          conclusion_elliptic_geometric_complexity_prime_register_elliptic_representation Ghist n) ∧
      (∀ n, conclusion_elliptic_geometric_complexity_axis_ratio_event Ghist threshold n) ∧
      (∀ n, conclusion_elliptic_geometric_complexity_hyperbolic_length_event Ghist threshold n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    rfl
  · intro n
    simpa [conclusion_elliptic_geometric_complexity_axis_ratio_event,
      conclusion_elliptic_geometric_complexity_axis_ratio,
      conclusion_elliptic_geometric_complexity_prime_register_elliptic_representation] using
      hGrow n
  · intro n
    simpa [conclusion_elliptic_geometric_complexity_hyperbolic_length_event,
      conclusion_elliptic_geometric_complexity_hyperbolic_length,
      conclusion_elliptic_geometric_complexity_prime_register_elliptic_representation] using
      hGrow n

end Omega.Conclusion

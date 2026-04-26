import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete radius readout used in the metric-defines-arithmetic wrapper. -/
def conclusion_metric_defines_arithmetic_radius (n : ℕ) : ℕ :=
  n

/-- Concrete self-isometries in the wrapper are the self-maps preserving the distinguished base
radius and the radius profile of every point. -/
def conclusion_metric_defines_arithmetic_isometry (F : ℕ → ℕ) : Prop :=
  F 1 = 1 ∧
    ∀ n : ℕ,
      conclusion_metric_defines_arithmetic_radius (F n) =
        conclusion_metric_defines_arithmetic_radius n

/-- Concrete paper-facing package for the arithmetic readout forced by the radius profile:
`1` is the unique point of radius `1`, every radius-preserving self-isometry is the identity,
and multiplication/`gcd`/`lcm`/divisibility/primality are uniquely recovered from the radius
equations. -/
def conclusion_metric_defines_arithmetic_statement : Prop :=
  (∃! u : ℕ, conclusion_metric_defines_arithmetic_radius u = 1) ∧
    (∀ F : ℕ → ℕ, conclusion_metric_defines_arithmetic_isometry F → F = id) ∧
    (∀ x y : ℕ,
      ∃! z : ℕ,
        conclusion_metric_defines_arithmetic_radius z =
          conclusion_metric_defines_arithmetic_radius x *
            conclusion_metric_defines_arithmetic_radius y) ∧
    (∀ x y : ℕ,
      ∃! g : ℕ,
        conclusion_metric_defines_arithmetic_radius g = Nat.gcd x y) ∧
    (∀ x y : ℕ,
      ∃! l : ℕ,
        conclusion_metric_defines_arithmetic_radius l = Nat.lcm x y) ∧
    (∀ a b : ℕ, Nat.gcd a b = a ↔ a ∣ b) ∧
    (∀ p : ℕ,
      Nat.Prime p ↔
        1 < p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p)

/-- Paper label: `thm:conclusion-metric-defines-arithmetic`. -/
theorem paper_conclusion_metric_defines_arithmetic :
    conclusion_metric_defines_arithmetic_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨1, rfl, ?_⟩
    intro u hu
    simpa [conclusion_metric_defines_arithmetic_radius] using hu
  · intro F hF
    funext n
    have hFn :
        conclusion_metric_defines_arithmetic_radius (F n) =
          conclusion_metric_defines_arithmetic_radius n :=
      hF.2 n
    simpa [conclusion_metric_defines_arithmetic_radius] using hFn
  · intro x y
    refine ⟨x * y, by simp [conclusion_metric_defines_arithmetic_radius], ?_⟩
    intro z hz
    simpa [conclusion_metric_defines_arithmetic_radius] using hz
  · intro x y
    refine ⟨Nat.gcd x y, by simp [conclusion_metric_defines_arithmetic_radius], ?_⟩
    intro g hg
    simpa [conclusion_metric_defines_arithmetic_radius] using hg
  · intro x y
    refine ⟨Nat.lcm x y, by simp [conclusion_metric_defines_arithmetic_radius], ?_⟩
    intro l hl
    simpa [conclusion_metric_defines_arithmetic_radius] using hl
  · intro a b
    exact Nat.gcd_eq_left_iff_dvd
  · intro p
    simpa using (Nat.prime_def (p := p))

end Omega.Conclusion

import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete denominator-scale data for the Euler--Kronecker local/global separation package. -/
structure conclusion_euler_kronecker_local_exact_global_nonautomatic_data where
  conclusion_euler_kronecker_local_exact_global_nonautomatic_alpha : ℝ
  conclusion_euler_kronecker_local_exact_global_nonautomatic_localScale : ℕ → ℚ
  conclusion_euler_kronecker_local_exact_global_nonautomatic_globalScale : ℕ → ℚ
  conclusion_euler_kronecker_local_exact_global_nonautomatic_gap : ℝ

/-- Transcendence proxy: no nonzero quadratic rational relation vanishes at `alpha`. -/
def conclusion_euler_kronecker_local_exact_global_nonautomatic_data.alpha_transcendental
    (D : conclusion_euler_kronecker_local_exact_global_nonautomatic_data) : Prop :=
  ∀ a b c : ℚ,
    (a : ℝ) * D.conclusion_euler_kronecker_local_exact_global_nonautomatic_alpha ^ 2 +
        (b : ℝ) * D.conclusion_euler_kronecker_local_exact_global_nonautomatic_alpha +
          (c : ℝ) =
      0 →
      a = 0 ∧ b = 0 ∧ c = 0

/-- Exact local denominator transport plus the positive scale gap used for separation. -/
def conclusion_euler_kronecker_local_exact_global_nonautomatic_data.denominator_scale_exact_transport
    (D : conclusion_euler_kronecker_local_exact_global_nonautomatic_data) : Prop :=
  (∀ n,
      D.conclusion_euler_kronecker_local_exact_global_nonautomatic_localScale n =
        D.conclusion_euler_kronecker_local_exact_global_nonautomatic_globalScale n) ∧
    0 < D.conclusion_euler_kronecker_local_exact_global_nonautomatic_gap ∧
      ∀ n,
        (0 : ℚ) ≤
          D.conclusion_euler_kronecker_local_exact_global_nonautomatic_globalScale n -
            D.conclusion_euler_kronecker_local_exact_global_nonautomatic_localScale n

/-- The Ostrowski parameter is not quadratic over the rational denominator scale. -/
def conclusion_euler_kronecker_local_exact_global_nonautomatic_data.not_quadratic_ostrowski
    (D : conclusion_euler_kronecker_local_exact_global_nonautomatic_data) : Prop :=
  ∀ a b c : ℚ,
    a ≠ 0 →
      (a : ℝ) * D.conclusion_euler_kronecker_local_exact_global_nonautomatic_alpha ^ 2 +
            (b : ℝ) * D.conclusion_euler_kronecker_local_exact_global_nonautomatic_alpha +
          (c : ℝ) ≠
        0

/-- The local exact transport statement. -/
def conclusion_euler_kronecker_local_exact_global_nonautomatic_data.local_exact_transport
    (D : conclusion_euler_kronecker_local_exact_global_nonautomatic_data) : Prop :=
  ∀ n,
    D.conclusion_euler_kronecker_local_exact_global_nonautomatic_localScale n =
      D.conclusion_euler_kronecker_local_exact_global_nonautomatic_globalScale n

/-- Strict separation of the local exact transport from the global automaticity gap. -/
def conclusion_euler_kronecker_local_exact_global_nonautomatic_data.strict_separation
    (D : conclusion_euler_kronecker_local_exact_global_nonautomatic_data) : Prop :=
  0 < D.conclusion_euler_kronecker_local_exact_global_nonautomatic_gap ∧
    ∀ n,
      (0 : ℚ) ≤
        D.conclusion_euler_kronecker_local_exact_global_nonautomatic_globalScale n -
          D.conclusion_euler_kronecker_local_exact_global_nonautomatic_localScale n

/-- Paper label: `prop:conclusion-euler-kronecker-local-exact-global-nonautomatic`. -/
theorem paper_conclusion_euler_kronecker_local_exact_global_nonautomatic
    (D : conclusion_euler_kronecker_local_exact_global_nonautomatic_data)
    (htrans : D.alpha_transcendental)
    (hlocal : D.denominator_scale_exact_transport) :
    D.not_quadratic_ostrowski ∧ D.local_exact_transport ∧ D.strict_separation := by
  rcases hlocal with ⟨htransport, hgap, hscale⟩
  refine ⟨?_, htransport, hgap, hscale⟩
  intro a b c ha hzero
  exact ha (htrans a b c hzero).1

end Omega.Conclusion

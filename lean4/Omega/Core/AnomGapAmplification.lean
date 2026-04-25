import Mathlib.Tactic

namespace Omega.POM

/-- Anomaly amplification: multiply the gap `a` by the iteration count `q`.
    cor:pom-anom-gap-amplification-completeness -/
def anomAmp (a : ℝ) (q : ℕ) : ℝ := (q : ℝ) * a

/-- Paper-facing statement of the POM anomaly gap amplification law.
    prop:pom-anom-gap-amplification -/
theorem paper_pom_anom_gap_amplification (q : Nat) (a : Real) :
    anomAmp a q = (q : Real) * a := by
  rfl

/-- Base: zero iterations give zero amplification.
    cor:pom-anom-gap-amplification-completeness -/
theorem anomAmp_zero (a : ℝ) : anomAmp a 0 = 0 := by
  unfold anomAmp; simp

/-- Recurrence: each iteration adds `a`.
    cor:pom-anom-gap-amplification-completeness -/
theorem anomAmp_succ (a : ℝ) (q : ℕ) :
    anomAmp a (q + 1) = anomAmp a q + a := by
  unfold anomAmp; push_cast; ring

/-- Archimedean completeness: any non-zero gap reaches any threshold after
    enough amplifications.
    cor:pom-anom-gap-amplification-completeness -/
theorem anomAmp_reaches_threshold (a : ℝ) (ha : a ≠ 0) (τ : ℝ) (_hτ : 0 < τ) :
    ∃ q : ℕ, 2 ≤ q ∧ τ ≤ |anomAmp a q| := by
  have habs : 0 < |a| := abs_pos.mpr ha
  obtain ⟨n, hn⟩ := exists_nat_gt (τ / |a|)
  refine ⟨max 2 n, le_max_left _ _, ?_⟩
  unfold anomAmp
  rw [abs_mul, Nat.abs_cast]
  have hnle : (n : ℝ) ≤ (max 2 n : ℕ) := by
    exact_mod_cast Nat.le_max_right 2 n
  have hτdiv : τ / |a| < (n : ℝ) := hn
  have hτ_lt : τ < (n : ℝ) * |a| := by
    rw [div_lt_iff₀ habs] at hτdiv
    exact hτdiv
  have : τ ≤ ((max 2 n : ℕ) : ℝ) * |a| := by
    have h1 : (n : ℝ) * |a| ≤ ((max 2 n : ℕ) : ℝ) * |a| :=
      mul_le_mul_of_nonneg_right hnle (le_of_lt habs)
    linarith
  exact this

/-- Converse: if the amplification stays bounded for every `q ≥ 2`, the gap
    vanishes.
    cor:pom-anom-gap-amplification-completeness -/
theorem anomAmp_zero_of_bounded (a : ℝ) (τ : ℝ) (hτ : 0 < τ)
    (h : ∀ q : ℕ, 2 ≤ q → |anomAmp a q| < τ) :
    a = 0 := by
  by_contra ha
  obtain ⟨q, hq2, hqτ⟩ := anomAmp_reaches_threshold a ha τ hτ
  exact absurd (h q hq2) (not_lt.mpr hqτ)

/-- Paper package: POM anomaly gap amplification completeness.
    cor:pom-anom-gap-amplification-completeness -/
theorem paper_pom_anom_gap_amplification_completeness :
    (∀ a : ℝ, anomAmp a 0 = 0) ∧
    (∀ (a : ℝ) (q : ℕ), anomAmp a (q + 1) = anomAmp a q + a) ∧
    (∀ (a : ℝ), a ≠ 0 → ∀ (τ : ℝ), 0 < τ →
      ∃ q : ℕ, 2 ≤ q ∧ τ ≤ |anomAmp a q|) ∧
    (∀ (a τ : ℝ), 0 < τ → (∀ q : ℕ, 2 ≤ q → |anomAmp a q| < τ) → a = 0) :=
  ⟨anomAmp_zero, anomAmp_succ,
   fun a ha τ hτ => anomAmp_reaches_threshold a ha τ hτ,
   anomAmp_zero_of_bounded⟩

end Omega.POM

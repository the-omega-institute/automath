import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The one-step loss on the multiplicative ray `a, ab, ab^2, ...`. -/
def conclusion_multiplicative_ray_total_freezing_equivalences_loss
    (P : ℕ → ℝ) (a b k : ℕ) : ℝ :=
  (b : ℝ) * P (a * b ^ k) - P (a * b ^ (k + 1))

/-- The escort entropy rate normalized by the positive factor `b - 1`. -/
def conclusion_multiplicative_ray_total_freezing_equivalences_escort
    (P : ℕ → ℝ) (a b k : ℕ) : ℝ :=
  conclusion_multiplicative_ray_total_freezing_equivalences_loss P a b k / ((b : ℝ) - 1)

/-- The finite ray potential obtained by summing all losses up to depth `N`. -/
def conclusion_multiplicative_ray_total_freezing_equivalences_total
    (P : ℕ → ℝ) (a b N : ℕ) : ℝ :=
  ∑ k : Fin N, conclusion_multiplicative_ray_total_freezing_equivalences_loss P a b k.val

/-- Finite concrete form of the four equivalent total-freezing conditions on a ray. -/
def conclusion_multiplicative_ray_total_freezing_equivalences_statement : Prop :=
  ∀ (P : ℕ → ℝ) (a b N : ℕ), 1 ≤ a → 2 ≤ b →
    (∀ k : Fin N, 0 ≤
      conclusion_multiplicative_ray_total_freezing_equivalences_loss P a b k.val) →
    let totalZero :=
      conclusion_multiplicative_ray_total_freezing_equivalences_total P a b N = 0
    let allLossZero :=
      ∀ k : Fin N,
        conclusion_multiplicative_ray_total_freezing_equivalences_loss P a b k.val = 0
    let allPressureLocked :=
      ∀ k : Fin N, P (a * b ^ (k.val + 1)) = (b : ℝ) * P (a * b ^ k.val)
    let allEscortZero :=
      ∀ k : Fin N,
        conclusion_multiplicative_ray_total_freezing_equivalences_escort P a b k.val = 0
    (totalZero ↔ allLossZero) ∧ (allLossZero ↔ allPressureLocked) ∧
      (allLossZero ↔ allEscortZero)

/-- Paper label: `thm:conclusion-multiplicative-ray-total-freezing-equivalences`. -/
theorem paper_conclusion_multiplicative_ray_total_freezing_equivalences :
    conclusion_multiplicative_ray_total_freezing_equivalences_statement := by
  intro P a b N _ha hb hnonneg
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · unfold conclusion_multiplicative_ray_total_freezing_equivalences_total
    simpa using
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun k : Fin N =>
          conclusion_multiplicative_ray_total_freezing_equivalences_loss P a b k.val)
        (fun k _hk => hnonneg k))
  · constructor
    · intro h k
      specialize h k
      unfold conclusion_multiplicative_ray_total_freezing_equivalences_loss at h
      linarith
    · intro h k
      specialize h k
      unfold conclusion_multiplicative_ray_total_freezing_equivalences_loss
      linarith
  · have hbne : ((b : ℝ) - 1) ≠ 0 := by
      have hbgt : (1 : ℝ) < b := by exact_mod_cast hb
      linarith
    constructor
    · intro h k
      unfold conclusion_multiplicative_ray_total_freezing_equivalences_escort
      rw [h k]
      simp
    · intro h k
      specialize h k
      unfold conclusion_multiplicative_ray_total_freezing_equivalences_escort at h
      rw [div_eq_zero_iff] at h
      exact h.resolve_right hbne

end

end Omega.Conclusion

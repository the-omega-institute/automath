import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The chapter-local finite Stieltjes-shadow partial sum. -/
noncomputable def xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_shadow
    (term : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 N, term n

/-- The finite reindexing identity obtained by splitting off the `n = 2` term. -/
def xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_split
    (term : ℕ → ℂ) (N : ℕ) : Prop :=
  2 ≤ N →
    xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_shadow term N =
      term 2 + ∑ n ∈ Finset.Icc 3 N, term n

/-- Coefficient recurrence for the homogeneous analytic-germ scaling equation. -/
def xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_homogeneous
    (lambda : ℂ) (c : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, c (n + 1) = lambda * c n

/-- Concrete statement package for the Stieltjes shadow finite recurrence and uniqueness. -/
def xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_statement : Prop :=
  (∀ (term : ℕ → ℂ) (N : ℕ),
    xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_split term N) ∧
    (∀ (lambda : ℂ) (c d : ℕ → ℂ),
      c 0 = d 0 →
        xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_homogeneous
            lambda c →
          xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_homogeneous
            lambda d →
            c = d)

/-- Paper label: `thm:xi-time-part9vk-resonance-stieltjes-shadow-renormalization-uniqueness`.

The finite shadow identity follows by splitting off the bottom endpoint of the interval.
Uniqueness of the analytic germ is coefficientwise induction for the homogeneous affine scaling
recurrence. -/
theorem paper_xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness :
    xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_statement := by
  refine ⟨?_, ?_⟩
  · intro term N hN
    refine Nat.le_induction ?base ?step N hN
    ·
      simp [xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_shadow]
    ·
      intro N hN ih
      have hsum₂ :
          (∑ n ∈ Finset.Icc 2 (N + 1), term n) =
            (∑ n ∈ Finset.Icc 2 N, term n) + term (N + 1) := by
        rw [Finset.sum_Icc_succ_top (a := 2) (b := N) (by omega) (fun n => term n)]
      have hsum₃ :
          (∑ n ∈ Finset.Icc 3 (N + 1), term n) =
            (∑ n ∈ Finset.Icc 3 N, term n) + term (N + 1) := by
        rw [Finset.sum_Icc_succ_top (a := 3) (b := N) (by omega) (fun n => term n)]
      dsimp [xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_split,
        xi_time_part9vk_resonance_stieltjes_shadow_renormalization_uniqueness_shadow] at ih ⊢
      rw [hsum₂, hsum₃, ih]
      ring
  · intro lambda c d h0 hc hd
    funext n
    induction n with
    | zero => exact h0
    | succ n ih =>
        rw [hc n, hd n, ih]

end Omega.Zeta

import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The paper's dyadic base `B = 2^L`, specialized to integer coefficients. -/
def xi_time_part9w_holographic_first_difference_valuation_base (L : ℕ) : ℤ :=
  2 ^ L

/-- The residual term after factoring out the common prefix contribution `B^τ`. -/
def xi_time_part9w_holographic_first_difference_valuation_tail (L : ℕ) (δ z : ℤ) : ℤ :=
  δ + xi_time_part9w_holographic_first_difference_valuation_base L * z

/-- The concrete address difference for a first mismatch at depth `τ + 1`, specialized to the
primitive address vector `v = 1`. -/
def xi_time_part9w_holographic_first_difference_valuation_gap
    (L τ : ℕ) (δ z : ℤ) : ℤ :=
  xi_time_part9w_holographic_first_difference_valuation_base L ^ τ *
    xi_time_part9w_holographic_first_difference_valuation_tail L δ z

private lemma xi_time_part9w_holographic_first_difference_valuation_base_pos (L : ℕ) :
    0 < xi_time_part9w_holographic_first_difference_valuation_base L := by
  simp [xi_time_part9w_holographic_first_difference_valuation_base]

private lemma xi_time_part9w_holographic_first_difference_valuation_tail_not_base_dvd
    (L : ℕ) (δ z : ℤ) (hδ0 : δ ≠ 0)
    (hδbound :
      |δ| < xi_time_part9w_holographic_first_difference_valuation_base L) :
    ¬ xi_time_part9w_holographic_first_difference_valuation_base L ∣
        xi_time_part9w_holographic_first_difference_valuation_tail L δ z := by
  intro htail
  let B : ℤ := xi_time_part9w_holographic_first_difference_valuation_base L
  have hBpos : 0 < B := xi_time_part9w_holographic_first_difference_valuation_base_pos L
  have hBz : B ∣ B * z := ⟨z, by simp [B, mul_comm]⟩
  have hδdiv : B ∣ δ := by
    simpa [B, xi_time_part9w_holographic_first_difference_valuation_tail, sub_eq_add_neg,
      add_assoc] using dvd_sub htail hBz
  rcases hδdiv with ⟨k, hk⟩
  have hk0 : k ≠ 0 := by
    intro hk0
    apply hδ0
    simp [hk, hk0]
  have hkabs : (1 : ℤ) ≤ |k| := by
    have hkabs_pos : 0 < |k| := by
      simpa using abs_pos.mpr hk0
    omega
  have habs : |δ| = B * |k| := by
    rw [hk, abs_mul, abs_of_nonneg (le_of_lt hBpos)]
  have hBle : B ≤ |δ| := by
    rw [habs]
    nlinarith [hBpos, hkabs]
  linarith

/-- Paper label: `thm:xi-time-part9w-holographic-first-difference-valuation`.
After expanding the first mismatch and factoring out the common prefix power `B^τ`, the remaining
tail is `δ + B * z`. The strict bound `|δ| < B = 2^L` rules out one more factor of `B`, so the
address difference lies in `B^τ ℤ \ B^(τ+1) ℤ`. -/
theorem paper_xi_time_part9w_holographic_first_difference_valuation
    (L τ : ℕ) (δ z : ℤ) (hδ0 : δ ≠ 0)
    (hδbound :
      |δ| < xi_time_part9w_holographic_first_difference_valuation_base L) :
    let B := xi_time_part9w_holographic_first_difference_valuation_base L
    let Δ := xi_time_part9w_holographic_first_difference_valuation_gap L τ δ z
    B ^ τ ∣ Δ ∧ ¬ B ^ (τ + 1) ∣ Δ := by
  dsimp
  refine ⟨⟨xi_time_part9w_holographic_first_difference_valuation_tail L δ z, rfl⟩, ?_⟩
  intro hhigh
  let B : ℤ := xi_time_part9w_holographic_first_difference_valuation_base L
  rcases hhigh with ⟨k, hk⟩
  have hBne : B ≠ 0 := by
    exact ne_of_gt (xi_time_part9w_holographic_first_difference_valuation_base_pos L)
  have hpow_ne : B ^ τ ≠ 0 := pow_ne_zero _ hBne
  have hfactor :
      B ^ τ * xi_time_part9w_holographic_first_difference_valuation_tail L δ z =
        B ^ τ * (B * k) := by
    calc
      B ^ τ * xi_time_part9w_holographic_first_difference_valuation_tail L δ z =
          B ^ (τ + 1) * k := by
            simpa [B, xi_time_part9w_holographic_first_difference_valuation_gap] using hk
      _ = B ^ τ * (B * k) := by
            simp [pow_succ, mul_assoc]
  have htail_eq :
      xi_time_part9w_holographic_first_difference_valuation_tail L δ z = B * k := by
    exact mul_left_cancel₀ hpow_ne hfactor
  have htail_dvd :
      B ∣ xi_time_part9w_holographic_first_difference_valuation_tail L δ z := ⟨k, htail_eq⟩
  exact xi_time_part9w_holographic_first_difference_valuation_tail_not_base_dvd
    L δ z hδ0 hδbound htail_dvd

end Omega.Zeta

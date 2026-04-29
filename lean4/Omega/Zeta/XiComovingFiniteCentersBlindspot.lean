import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_comoving_finite_centers_blindspot (H0 T : ℝ) (centers : Finset ℝ) (hH0 : 0 < H0) :
    (∃ γ : ℝ, ∀ x ∈ centers, H0 ≤ |γ - x|) ∧
      ((∀ γ ∈ Set.Icc (-T) T, ∃ x ∈ centers, |γ - x| < H0) →
        Nat.ceil (T / H0) ≤ centers.card) := by
  classical
  refine ⟨?_, ?_⟩
  · by_cases hcenters : centers.Nonempty
    · refine ⟨centers.max' hcenters + H0, ?_⟩
      intro x hx
      have hxle : x ≤ centers.max' hcenters := Finset.le_max' _ _ hx
      have hnonneg : 0 ≤ (centers.max' hcenters + H0) - x := by
        linarith
      rw [abs_of_nonneg hnonneg]
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hcenters ⟨x, hx⟩)
  · intro hcover
    by_cases hT : 0 < T
    · let N : ℕ := Nat.ceil (T / H0)
      have hNpos : 0 < N := by
        dsimp [N]
        exact Nat.ceil_pos.2 (div_pos hT hH0)
      let sample : Fin N → ℝ := fun i => -T + (2 : ℝ) * (i : ℝ) * H0
      have hsample_mem : ∀ i : Fin N, sample i ∈ Set.Icc (-T) T := by
        intro i
        have hi_lt_nat : i.1 < Nat.ceil (T / H0) := by
          simpa [N] using i.2
        have hi_lt : (i : ℝ) < T / H0 := Nat.lt_ceil.1 hi_lt_nat
        rw [lt_div_iff₀ hH0] at hi_lt
        have hi_nonneg : 0 ≤ (i : ℝ) := by
          exact_mod_cast Nat.zero_le i.1
        refine ⟨?_, ?_⟩
        · dsimp [sample]
          nlinarith
        · dsimp [sample]
          nlinarith
      have hsample_gap_of_lt : ∀ {i j : Fin N}, i < j → 2 * H0 ≤ |sample i - sample j| := by
        intro i j hij
        have hij_nat : i.1 < j.1 := hij
        have hstep_nat : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hij_nat
        have hstep : (i : ℝ) + 1 ≤ (j : ℝ) := by
          exact_mod_cast hstep_nat
        have hgap_real : (1 : ℝ) ≤ (j : ℝ) - i := by
          linarith
        have hdiff : sample j - sample i = 2 * ((j : ℝ) - i) * H0 := by
          dsimp [sample]
          ring
        have hnonneg : 0 ≤ sample j - sample i := by
          rw [hdiff]
          nlinarith [hgap_real, hH0]
        calc
          2 * H0 ≤ 2 * ((j : ℝ) - i) * H0 := by
            nlinarith [hgap_real, hH0]
          _ = sample j - sample i := by rw [hdiff]
          _ = |sample i - sample j| := by rw [abs_sub_comm, abs_of_nonneg hnonneg]
      have hsample_gap : ∀ {i j : Fin N}, i ≠ j → 2 * H0 ≤ |sample i - sample j| := by
        intro i j hij
        rcases lt_or_gt_of_ne hij with hijlt | hijgt
        · exact hsample_gap_of_lt hijlt
        · simpa [abs_sub_comm] using hsample_gap_of_lt hijgt
      have hsample_cover : ∀ i : Fin N, ∃ x : ℝ, x ∈ centers ∧ |sample i - x| < H0 := by
        intro i
        exact hcover (sample i) (hsample_mem i)
      choose pick hpick_mem hpick_dist using hsample_cover
      have hpick_inj :
          Function.Injective (fun i : Fin N => ({ val := pick i, property := hpick_mem i } :
            { x // x ∈ centers })) := by
        intro i j hij
        by_contra hne
        have hsame : pick i = pick j := congrArg Subtype.val hij
        have htri : |sample i - sample j| ≤ |sample i - pick i| + |pick i - sample j| := by
          simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using
            (abs_sub_le (sample i) (pick i) (sample j))
        have hsecond : |pick i - sample j| < H0 := by
          simpa [hsame, abs_sub_comm] using hpick_dist j
        have hlt : |sample i - sample j| < 2 * H0 := by
          linarith [htri, hpick_dist i, hsecond]
        have hge : 2 * H0 ≤ |sample i - sample j| := hsample_gap hne
        linarith
      have hcard :
          Fintype.card (Fin N) ≤ Fintype.card { x // x ∈ centers } := by
        exact Fintype.card_le_of_injective _ hpick_inj
      simpa [N] using hcard
    · have hratio_nonpos : T / H0 ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hT) hH0.le
      have hceil_zero : Nat.ceil (T / H0) = 0 := Nat.ceil_eq_zero.mpr hratio_nonpos
      simpa [hceil_zero]

end Omega.Zeta

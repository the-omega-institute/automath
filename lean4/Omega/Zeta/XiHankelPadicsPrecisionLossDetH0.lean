import Mathlib.Tactic

namespace Omega.Zeta

/-- Divisibility model for equality of one-dimensional `p^N` truncations. -/
def xi_hankel_padics_precision_loss_deth0_same_truncation
    (p N H H' : ℕ) : Prop :=
  p ^ N ∣ H' - H

/-- Division by a determinant with `p`-adic order `s` drops the guaranteed exponent by `s`. -/
def xi_hankel_padics_precision_loss_deth0_division_loss_statement : Prop :=
  ∀ p N s err : ℕ,
    Nat.Prime p →
      s ≤ N →
        p ^ N ∣ err →
          p ^ (N - s) ∣ err / p ^ s

/-- The one-dimensional sharpness witness from `H₀ = p^s`, `H₁ = 1`, `H₁' = 1 + p^N`. -/
def xi_hankel_padics_precision_loss_deth0_sharp_witness_statement : Prop :=
  ∀ p N s : ℕ,
    Nat.Prime p →
      s < N →
        xi_hankel_padics_precision_loss_deth0_same_truncation p N 1 (1 + p ^ N) ∧
          (1 + p ^ N - 1) / p ^ s = p ^ (N - s) ∧
            ¬ p ^ (N - s + 1) ∣ (1 + p ^ N - 1) / p ^ s

/-- Concrete precision-loss statement: adjugate/determinant division loses `s` digits, and the
`d = 1` witness shows the loss cannot generally be improved. -/
def xi_hankel_padics_precision_loss_deth0_statement : Prop :=
  xi_hankel_padics_precision_loss_deth0_division_loss_statement ∧
    xi_hankel_padics_precision_loss_deth0_sharp_witness_statement

theorem xi_hankel_padics_precision_loss_deth0_pow_mul_cancel
    {p N s k : ℕ} (hp : Nat.Prime p) (hs : s ≤ N) :
    p ^ N * k / p ^ s = p ^ (N - s) * k := by
  have hp_pos : 0 < p := hp.pos
  have hps_pos : 0 < p ^ s := pow_pos hp_pos s
  have hpow : p ^ N = p ^ s * p ^ (N - s) := by
    rw [← pow_add, Nat.add_sub_of_le hs]
  calc
    p ^ N * k / p ^ s = (p ^ s * (p ^ (N - s) * k)) / p ^ s := by
      rw [hpow]
      ac_rfl
    _ = p ^ (N - s) * k := by
      rw [Nat.mul_comm (p ^ s) (p ^ (N - s) * k)]
      exact Nat.mul_div_left (p ^ (N - s) * k) hps_pos

theorem xi_hankel_padics_precision_loss_deth0_division_loss :
    xi_hankel_padics_precision_loss_deth0_division_loss_statement := by
  intro p N s err hp hs herr
  rcases herr with ⟨k, rfl⟩
  refine ⟨k, ?_⟩
  exact xi_hankel_padics_precision_loss_deth0_pow_mul_cancel hp hs

theorem xi_hankel_padics_precision_loss_deth0_not_extra_dvd
    {p k : ℕ} (hp : Nat.Prime p) :
    ¬ p ^ (k + 1) ∣ p ^ k := by
  intro hdiv
  rcases hdiv with ⟨c, hc⟩
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  have hcancel : 1 = p * c := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc
      p ^ k * 1 = p ^ k := by rw [Nat.mul_one]
      _ = p ^ (k + 1) * c := hc
      _ = (p ^ k * p) * c := by rw [Nat.pow_succ]
      _ = p ^ k * (p * c) := by ac_rfl
  cases c with
  | zero =>
      norm_num at hcancel
  | succ c =>
      have hle : p ≤ p * Nat.succ c := Nat.le_mul_of_pos_right p (Nat.succ_pos c)
      have hp_le_one : p ≤ 1 := by
        rw [hcancel]
        exact hle
      have hp_two : 2 ≤ p := hp.two_le
      omega

theorem xi_hankel_padics_precision_loss_deth0_sharp_witness :
    xi_hankel_padics_precision_loss_deth0_sharp_witness_statement := by
  intro p N s hp hs
  have hsle : s ≤ N := Nat.le_of_lt hs
  refine ⟨?_, ?_, ?_⟩
  · unfold xi_hankel_padics_precision_loss_deth0_same_truncation
    simp
  · simpa using
      (xi_hankel_padics_precision_loss_deth0_pow_mul_cancel (p := p) (N := N) (s := s)
        (k := 1) hp hsle)
  · rw [show (1 + p ^ N - 1) / p ^ s = p ^ (N - s) by
        simpa using
          (xi_hankel_padics_precision_loss_deth0_pow_mul_cancel (p := p) (N := N)
            (s := s) (k := 1) hp hsle)]
    exact xi_hankel_padics_precision_loss_deth0_not_extra_dvd (p := p) (k := N - s) hp

/-- Paper label: `prop:xi-hankel-padics-precision-loss-detH0`. -/
theorem paper_xi_hankel_padics_precision_loss_deth0 :
    xi_hankel_padics_precision_loss_deth0_statement := by
  exact ⟨xi_hankel_padics_precision_loss_deth0_division_loss,
    xi_hankel_padics_precision_loss_deth0_sharp_witness⟩

end Omega.Zeta

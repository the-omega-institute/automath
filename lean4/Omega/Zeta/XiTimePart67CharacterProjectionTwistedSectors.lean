import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the twisted-sector character projection package on three residue classes. -/
structure xi_time_part67_character_projection_twisted_sectors_data where
  residueCount : ℕ → Fin 3 → ℝ
  rho : ℝ
  threshold : ℕ
  hrho_nonneg : 0 ≤ rho
  hrho_le_one : rho ≤ 1
  twisted_decay :
    ∀ n, threshold ≤ n →
      |((residueCount n) 0 - (((residueCount n) 0 + (residueCount n) 1 + (residueCount n) 2) / 3))| ≤
          rho ^ n ∧
        |((residueCount n) 2 - (((residueCount n) 0 + (residueCount n) 1 + (residueCount n) 2) / 3))| ≤
          rho ^ n

namespace xi_time_part67_character_projection_twisted_sectors_data

/-- Trivial-character component. -/
def xi_time_part67_character_projection_twisted_sectors_mean
    (c : Fin 3 → ℝ) : ℝ :=
  (c 0 + c 1 + c 2) / 3

/-- First nontrivial sector. -/
def xi_time_part67_character_projection_twisted_sectors_sector_one
    (c : Fin 3 → ℝ) : ℝ :=
  c 0 - xi_time_part67_character_projection_twisted_sectors_mean c

/-- Second nontrivial sector. -/
def xi_time_part67_character_projection_twisted_sectors_sector_two
    (c : Fin 3 → ℝ) : ℝ :=
  c 2 - xi_time_part67_character_projection_twisted_sectors_mean c

/-- Centered residue wave after removing the trivial character. -/
def xi_time_part67_character_projection_twisted_sectors_centered_wave
    (c : Fin 3 → ℝ) (x : Fin 3) : ℝ :=
  c x - xi_time_part67_character_projection_twisted_sectors_mean c

/-- The two explicit nontrivial basis characters. -/
def xi_time_part67_character_projection_twisted_sectors_basis_one (x : Fin 3) : ℝ :=
  if x = 0 then 1 else if x = 1 then -1 else 0

/-- The two explicit nontrivial basis characters. -/
def xi_time_part67_character_projection_twisted_sectors_basis_two (x : Fin 3) : ℝ :=
  if x = 2 then 1 else if x = 1 then -1 else 0

/-- Sum of the two twisted sectors. -/
def xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum
    (c : Fin 3 → ℝ) (x : Fin 3) : ℝ :=
  xi_time_part67_character_projection_twisted_sectors_sector_one c *
      xi_time_part67_character_projection_twisted_sectors_basis_one x +
    xi_time_part67_character_projection_twisted_sectors_sector_two c *
      xi_time_part67_character_projection_twisted_sectors_basis_two x

/-- Exact inversion into trivial plus nontrivial sectors. -/
def has_fourier_inversion
    (D : xi_time_part67_character_projection_twisted_sectors_data) : Prop :=
  ∀ n x,
    D.residueCount n x =
      xi_time_part67_character_projection_twisted_sectors_mean (D.residueCount n) +
        xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum
          (D.residueCount n) x

/-- Removing the trivial character leaves exactly the nontrivial sector sum. -/
def centered_wave_is_nontrivial_sector_sum
    (D : xi_time_part67_character_projection_twisted_sectors_data) : Prop :=
  ∀ n x,
    xi_time_part67_character_projection_twisted_sectors_centered_wave (D.residueCount n) x =
      xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum
        (D.residueCount n) x

/-- Exponential decay on each nontrivial twisted sector. -/
def nontrivial_sector_decay
    (D : xi_time_part67_character_projection_twisted_sectors_data) : Prop :=
  ∀ n, D.threshold ≤ n →
    |xi_time_part67_character_projection_twisted_sectors_sector_one (D.residueCount n)| ≤ D.rho ^ n ∧
      |xi_time_part67_character_projection_twisted_sectors_sector_two (D.residueCount n)| ≤ D.rho ^ n

/-- After the decay threshold, every centered residue class is bounded by the sum of the two
nontrivial-sector envelopes. -/
def large_sector_threshold
    (D : xi_time_part67_character_projection_twisted_sectors_data) : Prop :=
  ∀ n, D.threshold ≤ n →
    ∀ x,
      |xi_time_part67_character_projection_twisted_sectors_centered_wave (D.residueCount n) x| ≤
        2 * D.rho ^ n

/-- Threshold bounds persist along multiplicative towers. -/
def multiple_tower_inheritance
    (D : xi_time_part67_character_projection_twisted_sectors_data) : Prop :=
  ∀ m n, D.threshold ≤ n → 1 ≤ m →
    |xi_time_part67_character_projection_twisted_sectors_sector_one (D.residueCount (m * n))| ≤
        D.rho ^ (m * n) ∧
      |xi_time_part67_character_projection_twisted_sectors_sector_two (D.residueCount (m * n))| ≤
        D.rho ^ (m * n)

end xi_time_part67_character_projection_twisted_sectors_data

open xi_time_part67_character_projection_twisted_sectors_data

/-- Paper label: `thm:xi-time-part67-character-projection-twisted-sectors`. -/
theorem paper_xi_time_part67_character_projection_twisted_sectors
    (D : xi_time_part67_character_projection_twisted_sectors_data) :
    D.has_fourier_inversion ∧ D.centered_wave_is_nontrivial_sector_sum ∧ D.nontrivial_sector_decay ∧
      D.large_sector_threshold ∧ D.multiple_tower_inheritance := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    fin_cases x
    · simp [xi_time_part67_character_projection_twisted_sectors_mean,
        xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum,
        xi_time_part67_character_projection_twisted_sectors_sector_one,
        xi_time_part67_character_projection_twisted_sectors_sector_two,
        xi_time_part67_character_projection_twisted_sectors_basis_one,
        xi_time_part67_character_projection_twisted_sectors_basis_two]
    · simp [xi_time_part67_character_projection_twisted_sectors_mean,
        xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum,
        xi_time_part67_character_projection_twisted_sectors_sector_one,
        xi_time_part67_character_projection_twisted_sectors_sector_two,
        xi_time_part67_character_projection_twisted_sectors_basis_one,
        xi_time_part67_character_projection_twisted_sectors_basis_two]
      ring_nf
    · simp [xi_time_part67_character_projection_twisted_sectors_mean,
        xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum,
        xi_time_part67_character_projection_twisted_sectors_sector_one,
        xi_time_part67_character_projection_twisted_sectors_sector_two,
        xi_time_part67_character_projection_twisted_sectors_basis_one,
        xi_time_part67_character_projection_twisted_sectors_basis_two]
  · intro n x
    fin_cases x
    · simp [xi_time_part67_character_projection_twisted_sectors_centered_wave,
        xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum,
        xi_time_part67_character_projection_twisted_sectors_mean,
        xi_time_part67_character_projection_twisted_sectors_sector_one,
        xi_time_part67_character_projection_twisted_sectors_sector_two,
        xi_time_part67_character_projection_twisted_sectors_basis_one,
        xi_time_part67_character_projection_twisted_sectors_basis_two]
    · simp [xi_time_part67_character_projection_twisted_sectors_centered_wave,
        xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum,
        xi_time_part67_character_projection_twisted_sectors_mean,
        xi_time_part67_character_projection_twisted_sectors_sector_one,
        xi_time_part67_character_projection_twisted_sectors_sector_two,
        xi_time_part67_character_projection_twisted_sectors_basis_one,
        xi_time_part67_character_projection_twisted_sectors_basis_two]
      ring_nf
    · simp [xi_time_part67_character_projection_twisted_sectors_centered_wave,
        xi_time_part67_character_projection_twisted_sectors_nontrivial_sector_sum,
        xi_time_part67_character_projection_twisted_sectors_mean,
        xi_time_part67_character_projection_twisted_sectors_sector_one,
        xi_time_part67_character_projection_twisted_sectors_sector_two,
        xi_time_part67_character_projection_twisted_sectors_basis_one,
        xi_time_part67_character_projection_twisted_sectors_basis_two]
  · intro n hn
    simpa [xi_time_part67_character_projection_twisted_sectors_sector_one,
      xi_time_part67_character_projection_twisted_sectors_sector_two,
      xi_time_part67_character_projection_twisted_sectors_mean] using D.twisted_decay n hn
  · intro n hn x
    have hdecay := D.twisted_decay n hn
    have hrho_pow_nonneg : 0 ≤ D.rho ^ n := pow_nonneg D.hrho_nonneg n
    fin_cases x
    · simpa [xi_time_part67_character_projection_twisted_sectors_centered_wave,
        xi_time_part67_character_projection_twisted_sectors_sector_one,
        xi_time_part67_character_projection_twisted_sectors_mean] using
        le_trans hdecay.1 (by nlinarith)
    · have hmid : |((D.residueCount n) 1 -
          (((D.residueCount n) 0 + (D.residueCount n) 1 + (D.residueCount n) 2) / 3))| ≤
          2 * D.rho ^ n := by
        have hrewrite :
            (D.residueCount n) 1 -
                (((D.residueCount n) 0 + (D.residueCount n) 1 + (D.residueCount n) 2) / 3) =
              -(((D.residueCount n) 0 -
                    (((D.residueCount n) 0 + (D.residueCount n) 1 + (D.residueCount n) 2) / 3)) +
                  ((D.residueCount n) 2 -
                    (((D.residueCount n) 0 + (D.residueCount n) 1 + (D.residueCount n) 2) / 3))) := by
          ring
        rw [hrewrite, abs_neg]
        apply abs_le.mpr
        constructor <;> nlinarith [abs_le.mp hdecay.1, abs_le.mp hdecay.2]
      simpa [xi_time_part67_character_projection_twisted_sectors_centered_wave] using hmid
    · simpa [xi_time_part67_character_projection_twisted_sectors_centered_wave,
        xi_time_part67_character_projection_twisted_sectors_sector_two,
        xi_time_part67_character_projection_twisted_sectors_mean] using
        le_trans hdecay.2 (by nlinarith)
  · intro m n hn hm
    have hn_mul : n ≤ m * n := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hm
    have hmn : D.threshold ≤ m * n := le_trans hn hn_mul
    simpa [xi_time_part67_character_projection_twisted_sectors_sector_one,
      xi_time_part67_character_projection_twisted_sectors_sector_two,
      xi_time_part67_character_projection_twisted_sectors_mean] using D.twisted_decay (m * n) hmn

end

end Omega.Zeta

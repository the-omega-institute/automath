import Mathlib

namespace Omega.POM

open scoped BigOperators

theorem paper_pom_mod_congruence_renyi_divergence_codim {α : Type*} [Fintype α] [Nonempty α]
    (q : ℕ) (hq : 2 ≤ q) (p : α → ℝ) (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    let F : ℕ := Fintype.card α
    let Hq := ((1 : ℝ) / (1 - q : ℝ)) * Real.log (∑ a, p a ^ q)
    let Dqu := ((1 : ℝ) / (q - 1 : ℝ)) * Real.log (((F : ℝ) ^ (q - 1)) * ∑ a, p a ^ q)
    Dqu = Real.log F - Hq := by
  classical
  dsimp
  let S : ℝ := ∑ a, p a ^ q
  let F : ℕ := Fintype.card α
  have hF_pos_nat : 0 < F := by
    dsimp [F]
    exact Fintype.card_pos_iff.mpr ‹Nonempty α›
  have hF_pos : (0 : ℝ) < F := by
    exact_mod_cast hF_pos_nat
  have hF_ne : (F : ℝ) ≠ 0 := by
    exact ne_of_gt hF_pos
  have h_exists_pos : ∃ a, 0 < p a := by
    by_contra h
    have hp_zero : ∀ a, p a = 0 := by
      intro a
      have hnot : ¬0 < p a := by exact fun hpa => h ⟨a, hpa⟩
      exact le_antisymm (le_of_not_gt hnot) (hp_nonneg a)
    have : (∑ a, p a) = 0 := by simp [hp_zero]
    linarith [hp_sum]
  rcases h_exists_pos with ⟨a0, ha0_pos⟩
  have hS_pos : 0 < S := by
    dsimp [S]
    have hterm : 0 < p a0 ^ q := by positivity
    have hle : p a0 ^ q ≤ ∑ a, p a ^ q := by
      simpa using
        (Finset.single_le_sum (f := fun a : α => p a ^ q) (s := (Finset.univ : Finset α)) (a := a0)
          (fun a _ => by exact pow_nonneg (hp_nonneg a) _) (by simp : a0 ∈ (Finset.univ : Finset α)))
    exact lt_of_lt_of_le hterm hle
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hq1_nat : 1 ≤ q := by omega
  have hq1_pos : (0 : ℝ) < q - 1 := by
    exact_mod_cast (Nat.sub_pos_of_lt hq)
  have hq1_ne : (q - 1 : ℝ) ≠ 0 := by
    exact ne_of_gt hq1_pos
  calc
    ((1 : ℝ) / (q - 1 : ℝ)) * Real.log (((F : ℝ) ^ (q - 1)) * S)
        = ((1 : ℝ) / (q - 1 : ℝ)) * (Real.log ((F : ℝ) ^ (q - 1)) + Real.log S) := by
            rw [Real.log_mul (pow_ne_zero _ hF_ne) hS_ne]
    _ = ((1 : ℝ) / (q - 1 : ℝ)) * ((q - 1 : ℝ) * Real.log F + Real.log S) := by
      simpa [Nat.cast_sub hq1_nat] using
        congrArg (fun x => ((1 : ℝ) / (q - 1 : ℝ)) * (x + Real.log S)) (Real.log_pow (F : ℝ) (q - 1))
    _ = Real.log F + ((1 : ℝ) / (q - 1 : ℝ)) * Real.log S := by
      field_simp [hq1_ne]
    _ = Real.log F - (((1 : ℝ) / (1 - q : ℝ)) * Real.log S) := by
      have hden : ((1 : ℝ) / (q - 1 : ℝ)) = -((1 : ℝ) / (1 - q : ℝ)) := by
        have hsub : (1 - q : ℝ) = -(q - 1 : ℝ) := by ring
        rw [hsub]
        rw [div_neg]
        ring
      rw [hden]
      ring

end Omega.POM

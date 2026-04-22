import Mathlib
import Omega.POM.DiagonalRateSchurConcavity

open scoped BigOperators

namespace Omega.POM

/-- The extremal weight profile with one distinguished atom of mass `m` and the remaining mass
spread uniformly over the other `k` coordinates. -/
noncomputable def pom_diagonal_rate_max_atom_extremizer_profile (k : ℕ) (m : ℝ) :
    Fin (k + 1) → ℝ :=
  Fin.cases m fun _ => (1 - m) / k

lemma pom_diagonal_rate_max_atom_extremizer_profile_nonneg (k : ℕ) [NeZero k] {m : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    ∀ i : Fin (k + 1), 0 ≤ pom_diagonal_rate_max_atom_extremizer_profile k m i := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [pom_diagonal_rate_max_atom_extremizer_profile] using hm0
  · intro _
    have hk : 0 ≤ (k : ℝ) := by positivity
    have hmass : 0 ≤ 1 - m := by linarith
    simpa [pom_diagonal_rate_max_atom_extremizer_profile] using div_nonneg hmass hk

lemma pom_diagonal_rate_max_atom_extremizer_profile_sum (k : ℕ) [NeZero k] (m : ℝ) :
    ∑ i : Fin (k + 1), pom_diagonal_rate_max_atom_extremizer_profile k m i = 1 := by
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  rw [Fin.sum_univ_succ]
  simp [pom_diagonal_rate_max_atom_extremizer_profile]
  field_simp [hk]
  ring

lemma pom_diagonal_rate_max_atom_extremizer_profile_isProbabilityVector (k : ℕ) [NeZero k]
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    IsProbabilityVector (pom_diagonal_rate_max_atom_extremizer_profile k m) := by
  refine ⟨pom_diagonal_rate_max_atom_extremizer_profile_nonneg k hm0 hm1, ?_⟩
  exact pom_diagonal_rate_max_atom_extremizer_profile_sum k m

/-- Paper label: `thm:pom-diagonal-rate-max-atom-extremizer`. Fixing a designated atom of mass
`m`, the profile with uniform remaining mass is majorized by every competitor with the same total
mass and the same distinguished atom, so the Schur-concave diagonal rate is maximal there. -/
theorem paper_pom_diagonal_rate_max_atom_extremizer (k : ℕ) [NeZero k] (δ m : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (w : Fin (k + 1) → ℝ)
    (hw : IsProbabilityVector w) (hpeak : w 0 = m) :
    Majorizes w (pom_diagonal_rate_max_atom_extremizer_profile k m) ∧
      pomDiagonalRate (pom_diagonal_rate_max_atom_extremizer_profile k m) δ ≥
        pomDiagonalRate w δ := by
  let v := pom_diagonal_rate_max_atom_extremizer_profile k m
  have hv : IsProbabilityVector v :=
    pom_diagonal_rate_max_atom_extremizer_profile_isProbabilityVector k hm0 hm1
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hsum_v : ∑ i : Fin (k + 1), v i = 1 := hv.2
  have hsum_w : ∑ i : Fin (k + 1), w i = 1 := hw.2
  let tail : Fin k → ℝ := fun i => w i.succ
  have htail_sum_eq : m + ∑ i : Fin k, tail i = 1 := by
    rw [Fin.sum_univ_succ] at hsum_w
    simpa [tail, hpeak] using hsum_w
  have htail_sum : ∑ i : Fin k, tail i = 1 - m := by
    linarith
  have htail_sq :
      (∑ i : Fin k, tail i) ^ (2 : ℕ) ≤ (k : ℝ) * ∑ i : Fin k, (tail i) ^ (2 : ℕ) := by
    simpa [tail] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin k => tail i))
  have htail_sq_div :
      (1 - m) ^ (2 : ℕ) / (k : ℝ) ≤ ∑ i : Fin k, (tail i) ^ (2 : ℕ) := by
    have htail_sq' : (1 - m) ^ (2 : ℕ) ≤ (∑ i : Fin k, (tail i) ^ (2 : ℕ)) * (k : ℝ) := by
      simpa [htail_sum, mul_comm, mul_left_comm, mul_assoc] using htail_sq
    exact (div_le_iff₀ hkpos).2 htail_sq'
  have hv_sq :
      ∑ i : Fin (k + 1), (v i) ^ (2 : ℕ) = m ^ (2 : ℕ) + (1 - m) ^ (2 : ℕ) / (k : ℝ) := by
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
    rw [Fin.sum_univ_succ]
    simp [v, pom_diagonal_rate_max_atom_extremizer_profile]
    field_simp [hk]
  have hmajor_sq : ∑ i : Fin (k + 1), (v i) ^ (2 : ℕ) ≤ ∑ i : Fin (k + 1), (w i) ^ (2 : ℕ) := by
    rw [hv_sq, Fin.sum_univ_succ, hpeak]
    simpa [tail] using add_le_add_left htail_sq_div (m ^ (2 : ℕ))
  have hmajor : Majorizes w v := by
    refine ⟨by rw [hsum_v, hsum_w], hmajor_sq⟩
  refine ⟨hmajor, ?_⟩
  exact paper_pom_diagonal_rate_schur_concavity δ hδ0 hδ1 hv hw hmajor

end Omega.POM

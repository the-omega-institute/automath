import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

private lemma conclusion_tqft_genus_logconvexity_rigidity_equivalences_rat_cast_Z
    {ι : Type} [Fintype ι] (d : ι → ℕ) (Z : ℕ → ℚ)
    (hZ : ∀ g, Z g = ∑ i, ((d i : ℚ) ^ 2) / ((d i : ℚ) ^ (2 * g))) (g : ℕ) :
    (Z g : ℝ) = ∑ i, ((d i : ℝ) ^ 2) / ((d i : ℝ) ^ (2 * g)) := by
  rw [hZ g]
  norm_num

private lemma conclusion_tqft_genus_logconvexity_rigidity_equivalences_term_prev
    {g d : ℕ} :
    ((d : ℝ) ^ 2 / (d : ℝ) ^ (2 * (g - 1))) =
      ((d : ℝ) / (d : ℝ) ^ (g - 1)) ^ 2 := by
  rw [div_pow]
  congr 1
  ring

private lemma conclusion_tqft_genus_logconvexity_rigidity_equivalences_term_mid
    {g d : ℕ} (hg : 1 ≤ g) (hd : 0 < d) :
    ((d : ℝ) ^ 2 / (d : ℝ) ^ (2 * g)) =
      ((d : ℝ) / (d : ℝ) ^ (g - 1)) * (1 / (d : ℝ) ^ g) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hgpow : (d : ℝ) ^ (2 * g) = (d : ℝ) ^ g * (d : ℝ) ^ g := by
    rw [← pow_add, ← two_mul]
  have hpow : (d : ℝ) ^ g = (d : ℝ) ^ (g - 1) * (d : ℝ) := by
    calc
      (d : ℝ) ^ g = (d : ℝ) ^ ((g - 1) + 1) := by rw [Nat.sub_add_cancel hg]
      _ = (d : ℝ) ^ (g - 1) * (d : ℝ) := by rw [pow_succ]
  rw [hgpow, hpow]
  field_simp [hd']

private lemma conclusion_tqft_genus_logconvexity_rigidity_equivalences_term_next
    {g d : ℕ} (hd : 0 < d) :
    ((d : ℝ) ^ 2 / (d : ℝ) ^ (2 * (g + 1))) = (1 / (d : ℝ) ^ g) ^ 2 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hg : 2 * (g + 1) = 2 * g + 2 := by omega
  rw [hg, pow_add]
  field_simp [hd']
  ring

private lemma conclusion_tqft_genus_logconvexity_rigidity_equivalences_cross_eq
    {g a b : ℕ} (hg : 1 ≤ g) (ha : 0 < a) (hb : 0 < b)
    (h :
      ((a : ℝ) / (a : ℝ) ^ (g - 1)) * (1 / (b : ℝ) ^ g) =
        ((b : ℝ) / (b : ℝ) ^ (g - 1)) * (1 / (a : ℝ) ^ g)) :
    a = b := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have hapow : (a : ℝ) ^ g = (a : ℝ) ^ (g - 1) * (a : ℝ) := by
    calc
      (a : ℝ) ^ g = (a : ℝ) ^ ((g - 1) + 1) := by rw [Nat.sub_add_cancel hg]
      _ = (a : ℝ) ^ (g - 1) * (a : ℝ) := by rw [pow_succ]
  have hbpow : (b : ℝ) ^ g = (b : ℝ) ^ (g - 1) * (b : ℝ) := by
    calc
      (b : ℝ) ^ g = (b : ℝ) ^ ((g - 1) + 1) := by rw [Nat.sub_add_cancel hg]
      _ = (b : ℝ) ^ (g - 1) * (b : ℝ) := by rw [pow_succ]
  have hsquares : (a : ℝ) ^ 2 = (b : ℝ) ^ 2 := by
    rw [hapow, hbpow] at h
    field_simp [ha', hb'] at h
    simpa using h
  have hnonneg_a : 0 ≤ (a : ℝ) := by positivity
  have hnonneg_b : 0 ≤ (b : ℝ) := by positivity
  have hreal : (a : ℝ) = (b : ℝ) := (sq_eq_sq₀ hnonneg_a hnonneg_b).mp hsquares
  exact_mod_cast hreal

private lemma conclusion_tqft_genus_logconvexity_rigidity_equivalences_constant_of_eq
    {ι : Type} [Fintype ι] [Nonempty ι] (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (Z : ℕ → ℚ)
    (hZ : ∀ g, Z g = ∑ i, ((d i : ℚ) ^ 2) / ((d i : ℚ) ^ (2 * g)))
    {g : ℕ} (hg : 1 ≤ g) (heq : Z g ^ 2 = Z (g - 1) * Z (g + 1)) :
    ∃ c : ℕ, 0 < c ∧ ∀ i, d i = c := by
  classical
  let x : ι → ℝ := fun i => (d i : ℝ) / (d i : ℝ) ^ (g - 1)
  let y : ι → ℝ := fun i => 1 / (d i : ℝ) ^ g
  have hZprev :
      (Z (g - 1) : ℝ) = ∑ i, x i ^ 2 := by
    rw [conclusion_tqft_genus_logconvexity_rigidity_equivalences_rat_cast_Z d Z hZ]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact conclusion_tqft_genus_logconvexity_rigidity_equivalences_term_prev
  have hZmid :
      (Z g : ℝ) = ∑ i, x i * y i := by
    rw [conclusion_tqft_genus_logconvexity_rigidity_equivalences_rat_cast_Z d Z hZ]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact conclusion_tqft_genus_logconvexity_rigidity_equivalences_term_mid hg (hd i)
  have hZnext :
      (Z (g + 1) : ℝ) = ∑ i, y i ^ 2 := by
    rw [conclusion_tqft_genus_logconvexity_rigidity_equivalences_rat_cast_Z d Z hZ]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact conclusion_tqft_genus_logconvexity_rigidity_equivalences_term_next (g := g) (hd i)
  have hcs_eq :
      (∑ i, x i * y i) ^ 2 = (∑ i, x i ^ 2) * ∑ i, y i ^ 2 := by
    have heq_real : ((Z g : ℝ) ^ 2) = (Z (g - 1) : ℝ) * (Z (g + 1) : ℝ) := by
      exact_mod_cast heq
    simpa [hZprev, hZmid, hZnext] using heq_real
  let A : ℝ := ∑ i, x i ^ 2
  let B : ℝ := ∑ i, y i ^ 2
  let C : ℝ := ∑ i, x i * y i
  have hcs_eq' : C ^ 2 = A * B := by simpa [A, B, C] using hcs_eq
  have hB_pos : 0 < B := by
    dsimp [B]
    refine Finset.sum_pos' ?_ ?_
    · intro i _
      exact sq_nonneg (y i)
    · obtain ⟨i0⟩ := inferInstanceAs (Nonempty ι)
      refine ⟨i0, by simp, ?_⟩
      dsimp [y]
      have hden : 0 < (d i0 : ℝ) ^ g := by
        exact pow_pos (by exact_mod_cast hd i0) g
      exact sq_pos_of_pos (one_div_pos.mpr hden)
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have hidentity₁ :
      (∑ i, (B * x i - C * y i) ^ 2) =
        B ^ 2 * A - 2 * B * C * C + C ^ 2 * B := by
    calc
      (∑ i, (B * x i - C * y i) ^ 2) =
          ∑ i, (B ^ 2 * x i ^ 2 - 2 * B * C * (x i * y i) + C ^ 2 * y i ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      _ = B ^ 2 * A - 2 * B * C * C + C ^ 2 * B := by
        dsimp [A, B, C]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_mul]
  have hidentity :
      (∑ i, (B * x i - C * y i) ^ 2) = B * (A * B - C ^ 2) := by
    rw [hidentity₁]
    ring
  have hsum_zero : (∑ i, (B * x i - C * y i) ^ 2) = 0 := by
    rw [hidentity, hcs_eq']
    ring
  have hprop : ∀ i, B * x i = C * y i := by
    intro i
    have hterm : (B * x i - C * y i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (B * x j - C * y j))).mp
        hsum_zero i (by simp)
    nlinarith [sq_eq_zero_iff.mp hterm]
  obtain ⟨i0⟩ := inferInstanceAs (Nonempty ι)
  refine ⟨d i0, hd i0, ?_⟩
  intro i
  have hcross : x i * y i0 = x i0 * y i := by
    have hi := hprop i
    have hi0 := hprop i0
    have h1 : B * (x i * y i0) = B * (x i0 * y i) := by
      calc
        B * (x i * y i0) = (B * x i) * y i0 := by ring
        _ = (C * y i) * y i0 := by rw [hi]
        _ = (C * y i0) * y i := by ring
        _ = (B * x i0) * y i := by rw [hi0]
        _ = B * (x i0 * y i) := by ring
    exact mul_left_cancel₀ hB_ne h1
  exact conclusion_tqft_genus_logconvexity_rigidity_equivalences_cross_eq hg (hd i) (hd i0)
    (by simpa [x, y, mul_comm, mul_left_comm, mul_assoc] using hcross)

private lemma conclusion_tqft_genus_logconvexity_rigidity_equivalences_eq_of_constant
    {ι : Type} [Fintype ι] [Nonempty ι] (d : ι → ℕ)
    (Z : ℕ → ℚ)
    (hZ : ∀ g, Z g = ∑ i, ((d i : ℚ) ^ 2) / ((d i : ℚ) ^ (2 * g)))
    {c : ℕ} (hc : 0 < c) (hconst : ∀ i, d i = c) :
    ∃ g : ℕ, 1 ≤ g ∧ Z g ^ 2 = Z (g - 1) * Z (g + 1) := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  have hZ0 : Z 0 = (Fintype.card ι : ℚ) * (c : ℚ) ^ 2 := by
    rw [hZ 0]
    simp [hconst, div_eq_mul_inv]
  have hZ1 : Z 1 = (Fintype.card ι : ℚ) := by
    rw [hZ 1]
    simp [hconst, hcq]
  have hZ2 : Z 2 = (Fintype.card ι : ℚ) / (c : ℚ) ^ 2 := by
    rw [hZ 2]
    simp [hconst, div_eq_mul_inv, pow_succ]
    field_simp [hcq]
  rw [hZ0, hZ1, hZ2]
  field_simp [hcq]

/-- Paper label: `cor:conclusion-tqft-genus-logconvexity-rigidity-equivalences`. For a finite
positive genus moment tower, equality in one log-convexity step is equivalent to all fiber
multiplicities being constant. -/
theorem paper_conclusion_tqft_genus_logconvexity_rigidity_equivalences
    {ι : Type} [Fintype ι] [Nonempty ι] (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (Z : ℕ → ℚ)
    (hZ : ∀ g, Z g = ∑ i, ((d i : ℚ) ^ 2) / ((d i : ℚ) ^ (2 * g))) :
    ((∃ g : ℕ, 1 ≤ g ∧ Z g ^ 2 = Z (g - 1) * Z (g + 1)) ↔
      ∃ c : ℕ, 0 < c ∧ ∀ i, d i = c) := by
  constructor
  · rintro ⟨g, hg, heq⟩
    exact conclusion_tqft_genus_logconvexity_rigidity_equivalences_constant_of_eq d hd Z hZ hg heq
  · rintro ⟨c, hc, hconst⟩
    exact conclusion_tqft_genus_logconvexity_rigidity_equivalences_eq_of_constant d Z hZ hc hconst

end Omega.Conclusion

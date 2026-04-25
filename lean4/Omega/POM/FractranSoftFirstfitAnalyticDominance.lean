import Mathlib

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Partition function of the finite soft first-fit family. -/
def pom_fractran_soft_firstfit_analytic_dominance_partition
    (I : Finset ℕ) (u : ℝ) : ℝ :=
  Finset.sum I fun i => u ^ i

/-- Minimal-index normalization after factoring out the smallest feasible index. -/
def pom_fractran_soft_firstfit_analytic_dominance_normalized_partition
    (I : Finset ℕ) (u : ℝ) (i0 : ℕ) : ℝ :=
  Finset.sum I fun i => u ^ (i - i0)

/-- Normalized soft first-fit weight. -/
def pom_fractran_soft_firstfit_analytic_dominance_probability
    (I : Finset ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  if i ∈ I then
    u ^ i / pom_fractran_soft_firstfit_analytic_dominance_partition I u
  else
    0

lemma pom_fractran_soft_firstfit_analytic_dominance_partition_pos
    (I : Finset ℕ) (hI : I.Nonempty) {u : ℝ} (hu : 0 < u) :
    0 < pom_fractran_soft_firstfit_analytic_dominance_partition I u := by
  unfold pom_fractran_soft_firstfit_analytic_dominance_partition
  rcases hI with ⟨i0, hi0⟩
  have hi0pos : 0 < u ^ i0 := by positivity
  have hi0le :
      u ^ i0 ≤ Finset.sum I (fun i => u ^ i) := by
    simpa using
      (Finset.single_le_sum (f := fun i => u ^ i) (fun i _ => by positivity) hi0)
  exact lt_of_lt_of_le hi0pos hi0le

lemma pom_fractran_soft_firstfit_analytic_dominance_normalized_partition_pos
    (I : Finset ℕ) (hI : I.Nonempty) {u : ℝ} (hu : 0 < u) (i0 : ℕ) :
    0 < pom_fractran_soft_firstfit_analytic_dominance_normalized_partition I u i0 := by
  unfold pom_fractran_soft_firstfit_analytic_dominance_normalized_partition
  rcases hI with ⟨j0, hj0⟩
  have hj0pos : 0 < u ^ (j0 - i0) := by positivity
  have hj0le :
      u ^ (j0 - i0) ≤ Finset.sum I (fun i => u ^ (i - i0)) := by
    simpa using
      (Finset.single_le_sum (f := fun i => u ^ (i - i0)) (fun i _ => by positivity) hj0)
  exact lt_of_lt_of_le hj0pos hj0le

lemma pom_fractran_soft_firstfit_analytic_dominance_partition_factor
    (I : Finset ℕ) (hI : I.Nonempty) {u : ℝ} (hu : 0 < u) :
    pom_fractran_soft_firstfit_analytic_dominance_partition I u =
      u ^ I.min' hI *
        pom_fractran_soft_firstfit_analytic_dominance_normalized_partition I u (I.min' hI) := by
  unfold pom_fractran_soft_firstfit_analytic_dominance_partition
    pom_fractran_soft_firstfit_analytic_dominance_normalized_partition
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hmin : I.min' hI ≤ i := I.min'_le i hi
  have hexp : i = I.min' hI + (i - I.min' hI) := by omega
  nth_rewrite 1 [hexp]
  rw [pow_add]

lemma pom_fractran_soft_firstfit_analytic_dominance_probability_factor
    (I : Finset ℕ) (hI : I.Nonempty) {u : ℝ} (hu : 0 < u) {i : ℕ} (hi : i ∈ I) :
    pom_fractran_soft_firstfit_analytic_dominance_probability I u i =
      u ^ (i - I.min' hI) /
        pom_fractran_soft_firstfit_analytic_dominance_normalized_partition I u (I.min' hI) := by
  unfold pom_fractran_soft_firstfit_analytic_dominance_probability
  rw [if_pos hi, pom_fractran_soft_firstfit_analytic_dominance_partition_factor I hI hu]
  have hmin : I.min' hI ≤ i := I.min'_le i hi
  have hi' : u ^ i = u ^ I.min' hI * u ^ (i - I.min' hI) := by
    have hexp : i = I.min' hI + (i - I.min' hI) := by omega
    nth_rewrite 1 [hexp]
    rw [pow_add]
  rw [hi']
  field_simp [pow_ne_zero _ (ne_of_gt hu)]

lemma pom_fractran_soft_firstfit_analytic_dominance_cross_term
    {u1 u2 : ℝ} (hu1 : 0 < u1) (hu12 : u1 < u2) {i j : ℕ} (hij : i ≤ j) :
    u2 ^ i * u1 ^ j ≤ u1 ^ i * u2 ^ j := by
  have hj : j = i + (j - i) := by omega
  have hpow : u1 ^ (j - i) ≤ u2 ^ (j - i) := by
    gcongr
  have hu1j : u1 ^ j = u1 ^ i * u1 ^ (j - i) := by
    nth_rewrite 1 [hj]
    rw [pow_add]
  have hu2j : u2 ^ j = u2 ^ i * u2 ^ (j - i) := by
    nth_rewrite 1 [hj]
    rw [pow_add]
  have hnonneg : 0 ≤ u2 ^ i * u1 ^ i := by
    have hu2nonneg : 0 ≤ u2 := le_trans (le_of_lt hu1) hu12.le
    exact mul_nonneg (pow_nonneg hu2nonneg _) (pow_nonneg (le_of_lt hu1) _)
  calc
    u2 ^ i * u1 ^ j = (u2 ^ i * u1 ^ i) * u1 ^ (j - i) := by
      rw [hu1j]
      ring
    _ ≤ (u2 ^ i * u1 ^ i) * u2 ^ (j - i) := by
      exact mul_le_mul_of_nonneg_left hpow hnonneg
    _ = u1 ^ i * u2 ^ j := by
      rw [hu2j]
      ring

/-- Paper label: `prop:pom-fractran-soft-firstfit-analytic-dominance`. On any fixed nonempty
finite feasible-index set, the normalized soft first-fit family is given by explicit rational
functions on `(0,1]`, factoring out the minimal feasible index isolates the zero-temperature
concentration, and smaller temperatures first-order stochastically dominate larger ones along the
index order. -/
theorem paper_pom_fractran_soft_firstfit_analytic_dominance
    (I : Finset ℕ) (hI : I.Nonempty) :
    (∀ {u : ℝ}, 0 < u → u ≤ 1 →
      ∀ i,
        pom_fractran_soft_firstfit_analytic_dominance_probability I u i =
          if i ∈ I then
            u ^ i / pom_fractran_soft_firstfit_analytic_dominance_partition I u
          else
            0) ∧
      (∀ {u : ℝ}, 0 < u → u ≤ 1 →
        let i0 := I.min' hI
        pom_fractran_soft_firstfit_analytic_dominance_probability I u i0 =
            1 / pom_fractran_soft_firstfit_analytic_dominance_normalized_partition I u i0 ∧
          ∀ i ∈ I,
            pom_fractran_soft_firstfit_analytic_dominance_probability I u i =
              u ^ (i - i0) /
                pom_fractran_soft_firstfit_analytic_dominance_normalized_partition I u i0) ∧
      (∀ {u1 u2 : ℝ}, 0 < u1 → u1 < u2 → u2 ≤ 1 →
        ∀ i j, i ∈ I → j ∈ I → i ≤ j →
          pom_fractran_soft_firstfit_analytic_dominance_probability I u1 i *
              pom_fractran_soft_firstfit_analytic_dominance_probability I u2 j ≥
            pom_fractran_soft_firstfit_analytic_dominance_probability I u1 j *
              pom_fractran_soft_firstfit_analytic_dominance_probability I u2 i) ∧
      (∀ {u1 u2 : ℝ}, 0 < u1 → u1 < u2 → u2 ≤ 1 →
        ∀ t,
          Finset.sum (I.filter (fun i => i ≤ t)) (fun i => u2 ^ i) *
              pom_fractran_soft_firstfit_analytic_dominance_partition I u1 ≤
            Finset.sum (I.filter (fun i => i ≤ t)) (fun i => u1 ^ i) *
              pom_fractran_soft_firstfit_analytic_dominance_partition I u2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu hu1 i
    unfold pom_fractran_soft_firstfit_analytic_dominance_probability
    split_ifs <;> rfl
  · intro u hu hu1
    dsimp
    constructor
    · simpa using
        pom_fractran_soft_firstfit_analytic_dominance_probability_factor I hI hu (I.min'_mem hI)
    · intro i hi
      exact pom_fractran_soft_firstfit_analytic_dominance_probability_factor I hI hu hi
  · intro u1 u2 hu1 hu12 hu2 i j hi hj hij
    have hZ1pos :
        0 < pom_fractran_soft_firstfit_analytic_dominance_partition I u1 :=
      pom_fractran_soft_firstfit_analytic_dominance_partition_pos I hI hu1
    have hZ2pos :
        0 < pom_fractran_soft_firstfit_analytic_dominance_partition I u2 :=
      pom_fractran_soft_firstfit_analytic_dominance_partition_pos I hI (lt_trans hu1 hu12)
    rw [show pom_fractran_soft_firstfit_analytic_dominance_probability I u1 i =
        u1 ^ i / pom_fractran_soft_firstfit_analytic_dominance_partition I u1 by
          simp [pom_fractran_soft_firstfit_analytic_dominance_probability, hi]]
    rw [show pom_fractran_soft_firstfit_analytic_dominance_probability I u2 j =
        u2 ^ j / pom_fractran_soft_firstfit_analytic_dominance_partition I u2 by
          simp [pom_fractran_soft_firstfit_analytic_dominance_probability, hj]]
    rw [show pom_fractran_soft_firstfit_analytic_dominance_probability I u1 j =
        u1 ^ j / pom_fractran_soft_firstfit_analytic_dominance_partition I u1 by
          simp [pom_fractran_soft_firstfit_analytic_dominance_probability, hj]]
    rw [show pom_fractran_soft_firstfit_analytic_dominance_probability I u2 i =
        u2 ^ i / pom_fractran_soft_firstfit_analytic_dominance_partition I u2 by
          simp [pom_fractran_soft_firstfit_analytic_dominance_probability, hi]]
    have hcross := pom_fractran_soft_firstfit_analytic_dominance_cross_term hu1 hu12 hij
    have hden :
        0 < pom_fractran_soft_firstfit_analytic_dominance_partition I u1 *
            pom_fractran_soft_firstfit_analytic_dominance_partition I u2 := by
      exact mul_pos hZ1pos hZ2pos
    have hZ1nz : pom_fractran_soft_firstfit_analytic_dominance_partition I u1 ≠ 0 := ne_of_gt hZ1pos
    have hZ2nz : pom_fractran_soft_firstfit_analytic_dominance_partition I u2 ≠ 0 := ne_of_gt hZ2pos
    field_simp [hZ1nz, hZ2nz]
    nlinarith [hcross]
  · intro u1 u2 hu1 hu12 hu2 t
    let A : Finset ℕ := I.filter (fun i => i ≤ t)
    let B : Finset ℕ := I.filter (fun i => t < i)
    have hpart1 :
        pom_fractran_soft_firstfit_analytic_dominance_partition I u1 =
          Finset.sum A (fun i => u1 ^ i) + Finset.sum B (fun i => u1 ^ i) := by
      unfold A B pom_fractran_soft_firstfit_analytic_dominance_partition
      rw [← Finset.sum_filter_add_sum_filter_not (s := I) (p := fun i => i ≤ t)]
      congr 2
      ext i
      simp
    have hpart2 :
        pom_fractran_soft_firstfit_analytic_dominance_partition I u2 =
          Finset.sum A (fun i => u2 ^ i) + Finset.sum B (fun i => u2 ^ i) := by
      unfold A B pom_fractran_soft_firstfit_analytic_dominance_partition
      rw [← Finset.sum_filter_add_sum_filter_not (s := I) (p := fun i => i ≤ t)]
      congr 2
      ext i
      simp
    have hAB :
        Finset.sum A (fun i => u2 ^ i) * Finset.sum B (fun j => u1 ^ j) ≤
          Finset.sum A (fun i => u1 ^ i) * Finset.sum B (fun j => u2 ^ j) := by
      classical
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum ?_
      intro i hi
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro j hj
      have hile : i ≤ t := (Finset.mem_filter.mp hi).2
      have htj : t < j := (Finset.mem_filter.mp hj).2
      exact pom_fractran_soft_firstfit_analytic_dominance_cross_term hu1 hu12
        (le_trans hile (Nat.le_of_lt htj))
    rw [hpart1, hpart2]
    have hhead :
        Finset.sum A (fun i => u2 ^ i) *
            (Finset.sum A (fun i => u1 ^ i) + Finset.sum B (fun i => u1 ^ i)) ≤
          Finset.sum A (fun i => u1 ^ i) *
            (Finset.sum A (fun i => u2 ^ i) + Finset.sum B (fun i => u2 ^ i)) := by
      ring_nf
      nlinarith [hAB]
    simpa [A] using hhead

end

end Omega.POM

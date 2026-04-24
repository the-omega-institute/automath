import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.VisibleNegativeSpectrumVandermondeEnergy

namespace Omega.Conclusion

open scoped BigOperators

/-- The weight factor appearing in the visible negative-spectrum product formula. -/
noncomputable def conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product
    {κ : ℕ} (w : Fin κ → ℝ) : ℝ :=
  ∏ j, (w j) ^ (2 : ℕ)

/-- Sequence-level data for the pointwise degeneration dichotomy. -/
structure conclusion_visible_negative_spectrum_degeneration_dichotomy_data where
  κ : ℕ
  sigma : ℕ → Fin κ → ℝ
  w : ℕ → Fin κ → ℝ
  z : ℕ → Fin κ → ℂ
  hw_nonneg : ∀ n j, 0 ≤ w n j
  hpair_bound :
    ∀ n (p : Fin κ × Fin κ),
      p ∈ conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset κ →
      ‖z n p.2 - z n p.1‖ ≤ 2
  hproduct :
    ∀ n,
      (∏ i, |(-(sigma n i) ^ (2 : ℕ))|) =
        ((4 * Real.pi) ^ κ) *
          conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product (w n) *
            conclusion_visible_negative_spectrum_vandermonde_energy_pair_product (z n)
  weightFloor : ℝ
  hweightFloor_nonneg : 0 ≤ weightFloor
  hweightFloor_le : ∀ n j, weightFloor ≤ w n j

namespace conclusion_visible_negative_spectrum_degeneration_dichotomy_data

/-- Weight extinction means that one of the squared-weight factors vanishes. -/
def weight_extinction_at (D : conclusion_visible_negative_spectrum_degeneration_dichotomy_data)
    (n : ℕ) : Prop :=
  ∃ j, D.w n j = 0

/-- Node collision means that one unordered pair of Blaschke nodes coincides. -/
def node_collision_at (D : conclusion_visible_negative_spectrum_degeneration_dichotomy_data)
    (n : ℕ) : Prop :=
  ∃ p ∈ conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset D.κ,
    D.z n p.1 = D.z n p.2

/-- The packaged degeneration dichotomy: the pair product is uniformly disk-bounded, the visible
negative-spectrum product vanishes exactly by weight extinction or node collision, and a positive
uniform weight floor removes the first alternative. -/
def holds (D : conclusion_visible_negative_spectrum_degeneration_dichotomy_data) : Prop :=
  (∀ n,
    conclusion_visible_negative_spectrum_vandermonde_energy_pair_product (D.z n) ≤
      (2 : ℝ) ^ (4 * (conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset D.κ).card)) ∧
    (∀ n,
      (∏ i, |(-(D.sigma n i) ^ (2 : ℕ))|) = 0 ↔
        weight_extinction_at D n ∨ node_collision_at D n) ∧
      (0 < D.weightFloor →
        ∀ n, (∏ i, |(-(D.sigma n i) ^ (2 : ℕ))|) = 0 ↔ node_collision_at D n)

end conclusion_visible_negative_spectrum_degeneration_dichotomy_data

open conclusion_visible_negative_spectrum_degeneration_dichotomy_data

private lemma conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product_eq_zero_iff
    {κ : ℕ} (w : Fin κ → ℝ) :
    conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product w = 0 ↔
      ∃ j, w j = 0 := by
  unfold conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product
  constructor
  · intro hzero
    rw [Finset.prod_eq_zero_iff] at hzero
    rcases hzero with ⟨j, hj, hj0⟩
    refine ⟨j, sq_eq_zero_iff.mp ?_⟩
    simpa using hj0
  · rintro ⟨j, hj0⟩
    rw [Finset.prod_eq_zero_iff]
    exact ⟨j, Finset.mem_univ j, by simp [hj0]⟩

private lemma conclusion_visible_negative_spectrum_degeneration_dichotomy_pair_product_upper_bound
    (D : conclusion_visible_negative_spectrum_degeneration_dichotomy_data) (n : ℕ) :
    conclusion_visible_negative_spectrum_vandermonde_energy_pair_product (D.z n) ≤
      (2 : ℝ) ^ (4 * (conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset D.κ).card) := by
  unfold conclusion_visible_negative_spectrum_vandermonde_energy_pair_product
  have hle :
      Finset.prod (conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset D.κ) (fun p =>
          ‖D.z n p.2 - D.z n p.1‖ ^ (4 : ℕ)) ≤
        Finset.prod (conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset D.κ) (fun _ =>
          (2 : ℝ) ^ (4 : ℕ)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      positivity
    · intro p hp
      exact pow_le_pow_left₀ (by positivity) (D.hpair_bound n p hp) 4
  refine le_trans hle ?_
  simp [pow_mul]

private lemma conclusion_visible_negative_spectrum_degeneration_dichotomy_zero_iff
    (D : conclusion_visible_negative_spectrum_degeneration_dichotomy_data) (n : ℕ) :
    (∏ i, |(-(D.sigma n i) ^ (2 : ℕ))|) = 0 ↔
      weight_extinction_at D n ∨ node_collision_at D n := by
  constructor
  · intro hzero
    have hconst_ne : ((4 * Real.pi) ^ D.κ) ≠ 0 := by positivity
    have hzero' :
        conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product (D.w n) *
            conclusion_visible_negative_spectrum_vandermonde_energy_pair_product (D.z n) = 0 := by
      have hzero_formula :
          ((4 * Real.pi) ^ D.κ) *
              conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product (D.w n) *
                conclusion_visible_negative_spectrum_vandermonde_energy_pair_product (D.z n) = 0 := by
        rw [← D.hproduct n]
        exact hzero
      have hmul :
          ((4 * Real.pi) ^ D.κ) *
              (conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product (D.w n) *
                conclusion_visible_negative_spectrum_vandermonde_energy_pair_product (D.z n)) = 0 := by
        simpa [mul_assoc] using hzero_formula
      rcases mul_eq_zero.mp hmul with hconst | hrest
      · exact False.elim (hconst_ne hconst)
      · exact hrest
    rcases mul_eq_zero.mp hzero' with hweight | hpair
    · left
      exact
        (conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product_eq_zero_iff
          (D.w n)).mp hweight
    · right
      exact
        (conclusion_visible_negative_spectrum_vandermonde_energy_pair_product_eq_zero_iff
          (D.z n)).mp hpair
  · rintro (hweight | hpair)
    · rcases hweight with ⟨j, hj0⟩
      rw [D.hproduct n]
      have hweight0 :
          conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product (D.w n) = 0 :=
        (conclusion_visible_negative_spectrum_degeneration_dichotomy_weight_square_product_eq_zero_iff
          (D.w n)).mpr ⟨j, hj0⟩
      simp [hweight0]
    · rcases hpair with ⟨p, hp, hpEq⟩
      rw [D.hproduct n]
      have hpair0 :
          conclusion_visible_negative_spectrum_vandermonde_energy_pair_product (D.z n) = 0 :=
        (conclusion_visible_negative_spectrum_vandermonde_energy_pair_product_eq_zero_iff
          (D.z n)).mpr ⟨p, hp, hpEq⟩
      simp [hpair0]

/-- Paper label: `cor:conclusion-visible-negative-spectrum-degeneration-dichotomy`. The explicit
negative-spectrum factorization packages the only two pointwise degeneration mechanisms: weight
extinction or node collision. The disk bound gives a uniform control on the Vandermonde factor, and
a positive uniform weight floor rules out the extinction branch. -/
theorem paper_conclusion_visible_negative_spectrum_degeneration_dichotomy
    (D : conclusion_visible_negative_spectrum_degeneration_dichotomy_data) : holds D := by
  refine ⟨conclusion_visible_negative_spectrum_degeneration_dichotomy_pair_product_upper_bound D,
    conclusion_visible_negative_spectrum_degeneration_dichotomy_zero_iff D, ?_⟩
  intro hfloor n
  constructor
  · intro hzero
    rcases (conclusion_visible_negative_spectrum_degeneration_dichotomy_zero_iff D n).mp hzero with
      hweight | hpair
    · rcases hweight with ⟨j, hj0⟩
      have hpos : 0 < D.w n j := lt_of_lt_of_le hfloor (D.hweightFloor_le n j)
      rw [hj0] at hpos
      exact False.elim (lt_irrefl 0 hpos)
    · exact hpair
  · intro hpair
    exact (conclusion_visible_negative_spectrum_degeneration_dichotomy_zero_iff D n).mpr
      (Or.inr hpair)

end Omega.Conclusion

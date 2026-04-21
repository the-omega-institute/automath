import Mathlib

namespace Omega.POM

open Filter
open scoped Topology

noncomputable def fiberLayerMoment {α : Type*} [DecidableEq α]
    (X : Finset α) (d : α → ℝ) (q : ℕ) : ℝ :=
  X.sum (fun x => d x ^ q)

noncomputable def fiberLayerMeanMoment {α : Type*} [DecidableEq α]
    (X : Finset α) (d : α → ℝ) (q : ℕ) : ℝ :=
  fiberLayerMoment X d q / (X.card : ℝ)

noncomputable def fiberPZThresholdSet {α : Type*} [DecidableEq α]
    (X : Finset α) (d : α → ℝ) (q : ℕ) : Finset α :=
  X.filter (fun x => fiberLayerMeanMoment X d q / 2 ≤ d x ^ q)

noncomputable def fiberPZComplementSet {α : Type*} [DecidableEq α]
    (X : Finset α) (d : α → ℝ) (q : ℕ) : Finset α :=
  X.filter (fun x => ¬ fiberLayerMeanMoment X d q / 2 ≤ d x ^ q)

noncomputable def fiberPZLowerSequence (rq r2q : ℝ) (m : ℕ) : ℝ :=
  Real.exp (((m : ℝ) + 1) * (2 * Real.log rq - Real.log r2q) - Real.log 4)

lemma fiberPZ_mass_on_threshold {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : X.Nonempty) (d : α → ℝ) (q : ℕ)
    (hd : ∀ x ∈ X, 0 ≤ d x) :
    fiberLayerMoment (fiberPZThresholdSet X d q) d q ≥ fiberLayerMoment X d q / 2 := by
  classical
  have hcard_pos : 0 < (X.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hX
  have hComp_le :
      fiberLayerMoment (fiberPZComplementSet X d q) d q ≤
        (fiberPZComplementSet X d q).sum (fun _ => fiberLayerMeanMoment X d q / 2) := by
    unfold fiberLayerMoment fiberPZComplementSet
    refine Finset.sum_le_sum ?_
    intro x hx
    have hx' : ¬ fiberLayerMeanMoment X d q / 2 ≤ d x ^ q := (Finset.mem_filter.mp hx).2
    exact le_of_lt (lt_of_not_ge hx')
  have hComp_card :
      (fiberPZComplementSet X d q).sum (fun _ => fiberLayerMeanMoment X d q / 2) =
        ((fiberPZComplementSet X d q).card : ℝ) * (fiberLayerMeanMoment X d q / 2) := by
    simp
  have hComp_le_half :
      fiberLayerMoment (fiberPZComplementSet X d q) d q ≤ fiberLayerMoment X d q / 2 := by
    rw [hComp_card] at hComp_le
    have hcard_le_nat : (fiberPZComplementSet X d q).card ≤ X.card := by
      show (X.filter (fun x => ¬ fiberLayerMeanMoment X d q / 2 ≤ d x ^ q)).card ≤ X.card
      exact Finset.card_filter_le (s := X) (p := fun x => ¬ fiberLayerMeanMoment X d q / 2 ≤ d x ^ q)
    have hcard_le : (((fiberPZComplementSet X d q).card : ℝ)) ≤ X.card := by
      exact_mod_cast hcard_le_nat
    have hscale :
        ((fiberPZComplementSet X d q).card : ℝ) * (fiberLayerMeanMoment X d q / 2) ≤
          (X.card : ℝ) * (fiberLayerMeanMoment X d q / 2) := by
      have hmean_nonneg : 0 ≤ fiberLayerMeanMoment X d q := by
        unfold fiberLayerMeanMoment fiberLayerMoment
        refine div_nonneg ?_ hcard_pos.le
        exact Finset.sum_nonneg (by
          intro x hx
          exact pow_nonneg (hd x hx) _)
      gcongr
    have hmean_eval :
        (X.card : ℝ) * (fiberLayerMeanMoment X d q / 2) = fiberLayerMoment X d q / 2 := by
      have hcard_ne : (X.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
      unfold fiberLayerMeanMoment
      field_simp [hcard_ne]
    exact le_trans hComp_le (le_trans hscale (by simp [hmean_eval]))
  have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := X) (p := fun x => fiberLayerMeanMoment X d q / 2 ≤ d x ^ q) (f := fun x => d x ^ q)
  have hsum_eq :
      fiberLayerMoment (fiberPZThresholdSet X d q) d q +
          fiberLayerMoment (fiberPZComplementSet X d q) d q =
        fiberLayerMoment X d q := by
    unfold fiberLayerMoment fiberPZThresholdSet fiberPZComplementSet
    simpa [add_comm, add_left_comm, add_assoc] using hsplit
  linarith

lemma fiberPZ_count_mul_moment {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : X.Nonempty) (d : α → ℝ) (q : ℕ)
    (hd : ∀ x ∈ X, 0 ≤ d x) :
    fiberLayerMoment X d q ^ 2 ≤
      4 * ((fiberPZThresholdSet X d q).card : ℝ) * fiberLayerMoment X d (q * 2) := by
  classical
  have hhalf :
      fiberLayerMoment X d q / 2 ≤ fiberLayerMoment (fiberPZThresholdSet X d q) d q :=
    fiberPZ_mass_on_threshold X hX d q hd
  have hsq :
      fiberLayerMoment (fiberPZThresholdSet X d q) d q ^ 2 ≤
        ((fiberPZThresholdSet X d q).card : ℝ) *
          fiberLayerMoment (fiberPZThresholdSet X d q) d (q * 2) := by
    have hsq0 :=
      (sq_sum_le_card_mul_sum_sq (s := fiberPZThresholdSet X d q) (f := fun x => d x ^ q))
    simpa [fiberLayerMoment, pow_mul] using hsq0
  have hsquares_split := Finset.sum_filter_add_sum_filter_not
      (s := X) (p := fun x => fiberLayerMeanMoment X d q / 2 ≤ d x ^ q)
      (f := fun x => d x ^ (q * 2))
  have hsquare_le :
      fiberLayerMoment (fiberPZThresholdSet X d q) d (q * 2) ≤ fiberLayerMoment X d (q * 2) := by
    have hnonneg :
        0 ≤ fiberLayerMoment (fiberPZComplementSet X d q) d (q * 2) := by
      unfold fiberLayerMoment fiberPZComplementSet
      exact Finset.sum_nonneg (by
        intro x hx
        exact pow_nonneg (hd x ((Finset.mem_filter.mp hx).1)) _)
    have hsum_eq :
        fiberLayerMoment (fiberPZThresholdSet X d q) d (q * 2) +
            fiberLayerMoment (fiberPZComplementSet X d q) d (q * 2) =
          fiberLayerMoment X d (q * 2) := by
      unfold fiberLayerMoment fiberPZThresholdSet fiberPZComplementSet
      simpa [add_comm, add_left_comm, add_assoc] using hsquares_split
    linarith
  have hthreshold_nonneg : 0 ≤ fiberLayerMoment (fiberPZThresholdSet X d q) d q := by
    unfold fiberLayerMoment fiberPZThresholdSet
    exact Finset.sum_nonneg (by
      intro x hx
      exact pow_nonneg (hd x ((Finset.mem_filter.mp hx).1)) _)
  have hsq' :
      fiberLayerMoment (fiberPZThresholdSet X d q) d q ^ 2 ≤
        ((fiberPZThresholdSet X d q).card : ℝ) * fiberLayerMoment X d (q * 2) := by
    exact le_trans hsq (by gcongr)
  have hmoment_nonneg : 0 ≤ fiberLayerMoment X d q := by
    unfold fiberLayerMoment
    exact Finset.sum_nonneg (by
      intro x hx
      exact pow_nonneg (hd x hx) _)
  have htemp :
      (fiberLayerMoment X d q / 2) ^ 2 ≤
        ((fiberPZThresholdSet X d q).card : ℝ) * fiberLayerMoment X d (q * 2) := by
    nlinarith [hhalf, hsq', hthreshold_nonneg, hmoment_nonneg]
  nlinarith

lemma fiberPZ_count_lower {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : X.Nonempty) (d : α → ℝ) (q : ℕ)
    (hd : ∀ x ∈ X, 0 ≤ d x) :
    ((fiberPZThresholdSet X d q).card : ℝ) ≥
      fiberLayerMoment X d q ^ 2 / (4 * fiberLayerMoment X d (q * 2)) := by
  have hmain := fiberPZ_count_mul_moment X hX d q hd
  by_cases hzero : fiberLayerMoment X d (q * 2) = 0
  · simp [hzero]
  · have hsnonneg : 0 ≤ fiberLayerMoment X d (q * 2) := by
      unfold fiberLayerMoment
      exact Finset.sum_nonneg (by
        intro x hx
        exact pow_nonneg (hd x hx) _)
    have hden : 0 < 4 * fiberLayerMoment X d (q * 2) := by
      have hspos : 0 < fiberLayerMoment X d (q * 2) := by
        exact lt_of_le_of_ne hsnonneg (by simpa [eq_comm] using hzero)
      positivity
    rw [ge_iff_le]
    refine (div_le_iff₀ hden).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain

/-- Paper label: `prop:pom-spectrum-pz-lower`.
The finite-layer Paley--Zygmund threshold count is bounded below by the second-moment quotient,
and the associated explicit exponential lower sequence has the advertised logarithmic rate. -/
theorem paper_pom_spectrum_pz_lower {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : X.Nonempty) (d : α → ℝ) (q : ℕ)
    (hd : ∀ x ∈ X, 0 ≤ d x) (rq r2q : ℝ) :
    ((fiberPZThresholdSet X d q).card : ℝ) ≥
        fiberLayerMoment X d q ^ 2 / (4 * fiberLayerMoment X d (q * 2)) ∧
      ∀ m : ℕ,
        Real.log (fiberPZLowerSequence rq r2q m) / ((m : ℝ) + 1) =
          (2 * Real.log rq - Real.log r2q) - Real.log 4 / ((m : ℝ) + 1) := by
  refine ⟨fiberPZ_count_lower X hX d q hd, ?_⟩
  intro m
  unfold fiberPZLowerSequence
  rw [Real.log_exp]
  field_simp

end Omega.POM

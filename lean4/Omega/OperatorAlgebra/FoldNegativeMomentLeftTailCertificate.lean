import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldFiberMultiplicityTraceMoments
import Omega.POM.FiberSpectrumPZLower

namespace Omega.OperatorAlgebra

open FoldFiberMultiplicity
open Omega.POM

noncomputable section

private lemma singularNegativeMoment_pos_of_nonempty (D : FoldFiberMultiplicity) (s : ℕ)
    [Nonempty D.X] : 0 < D.singularNegativeMoment s := by
  classical
  rw [paper_fold_fiber_multiplicity_trace_moments D 0 s |>.2.2]
  have hterm_pos : ∀ x : D.X, 0 < (1 / (D.d x : ℝ)) ^ s := by
    intro x
    have hbase : 0 < 1 / (D.d x : ℝ) := by
      have hd : 0 < (D.d x : ℝ) := by exact_mod_cast D.d_pos x
      positivity
    exact pow_pos hbase _
  let x : D.X := Classical.choice (inferInstance : Nonempty D.X)
  have hxmem : x ∈ (Finset.univ : Finset D.X) := by simp
  exact lt_of_lt_of_le (hterm_pos x) (Finset.single_le_sum (fun y _ => le_of_lt (hterm_pos y)) hxmem)

private lemma threshold_condition_iff (D : FoldFiberMultiplicity) (s : ℕ) (x : D.X)
    (hcard : 0 < (Fintype.card D.X : ℝ)) (hmoment : 0 < D.singularNegativeMoment s) :
    D.singularNegativeMoment s / (Fintype.card D.X : ℝ) / 2 ≤ (1 / (D.d x : ℝ)) ^ s ↔
      (D.d x : ℝ) ^ s ≤ (2 * (Fintype.card D.X : ℝ)) / D.singularNegativeMoment s := by
  have hdx_pos : 0 < (D.d x : ℝ) := by
    exact_mod_cast D.d_pos x
  have hpow_pos : 0 < (D.d x : ℝ) ^ s := by positivity
  have hpow_ne : (D.d x : ℝ) ^ s ≠ 0 := ne_of_gt hpow_pos
  rw [show (1 / (D.d x : ℝ)) ^ s = 1 / ((D.d x : ℝ) ^ s) by
    rw [one_div]
    simp]
  constructor
  · intro h
    have h' : D.singularNegativeMoment s * (D.d x : ℝ) ^ s ≤ 2 * (Fintype.card D.X : ℝ) := by
      have := h
      field_simp [hcard.ne', hmoment.ne', hpow_ne] at this
      linarith
    exact (le_div_iff₀ hmoment).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h')
  · intro h
    have h' : D.singularNegativeMoment s * (D.d x : ℝ) ^ s ≤ 2 * (Fintype.card D.X : ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (le_div_iff₀ hmoment).1 h
    have : D.singularNegativeMoment s / (Fintype.card D.X : ℝ) / 2 ≤ 1 / ((D.d x : ℝ) ^ s) := by
      field_simp [hcard.ne', hmoment.ne', hpow_ne]
      linarith
    simpa

/-- Paper label: `prop:fold-negative-moment-left-tail-certificate`.
Applying the Paley--Zygmund lower-count estimate to `Y(x) = d(x)^{-s}` under the uniform law on
the finite fiber base gives a concrete left-tail certificate in terms of the negative moments. -/
theorem paper_fold_negative_moment_left_tail_certificate (D : FoldFiberMultiplicity) (s : ℕ)
    (hs : 0 < s) :
    (((Finset.univ.filter
        (fun x => (D.d x : ℝ) ^ s ≤
          (2 * (Fintype.card D.X : ℝ)) / D.singularNegativeMoment s)).card : ℝ) /
      (Fintype.card D.X : ℝ)) ≥
        (D.singularNegativeMoment s) ^ 2 /
          (4 * (Fintype.card D.X : ℝ) * D.singularNegativeMoment (2 * s)) := by
  classical
  let _ := hs
  by_cases hcard0 : Fintype.card D.X = 0
  · simp [hcard0]
  · have hcard_nat : 0 < Fintype.card D.X := Nat.pos_of_ne_zero hcard0
    have hcard : 0 < (Fintype.card D.X : ℝ) := by exact_mod_cast hcard_nat
    let d' : D.X → ℝ := fun x => 1 / (D.d x : ℝ)
    haveI : Nonempty D.X := Fintype.card_pos_iff.mp hcard_nat
    have hnonempty : (Finset.univ : Finset D.X).Nonempty := Finset.univ_nonempty
    have hd_nonneg : ∀ x ∈ (Finset.univ : Finset D.X), 0 ≤ d' x := by
      intro x hx
      positivity
    have hcount :=
      fiberPZ_count_lower (X := (Finset.univ : Finset D.X)) hnonempty d' s hd_nonneg
    have hmoment_s :
        fiberLayerMoment (Finset.univ : Finset D.X) d' s = D.singularNegativeMoment s := by
      symm
      simpa [d', fiberLayerMoment] using (paper_fold_fiber_multiplicity_trace_moments D 0 s).2.2
    have hmoment_2s :
        fiberLayerMoment (Finset.univ : Finset D.X) d' (2 * s) = D.singularNegativeMoment (2 * s) := by
      symm
      simpa [d', fiberLayerMoment] using (paper_fold_fiber_multiplicity_trace_moments D 0 (2 * s)).2.2
    have hmoment_s2 :
        fiberLayerMoment (Finset.univ : Finset D.X) d' (s * 2) = D.singularNegativeMoment (2 * s) := by
      simpa [Nat.mul_comm] using hmoment_2s
    have hmoment_pos : 0 < D.singularNegativeMoment s :=
      singularNegativeMoment_pos_of_nonempty D s
    have hthreshold :
        fiberPZThresholdSet (Finset.univ : Finset D.X) d' s =
          Finset.univ.filter
            (fun x => (D.d x : ℝ) ^ s ≤
              (2 * (Fintype.card D.X : ℝ)) / D.singularNegativeMoment s) := by
      ext x
      simp only [fiberPZThresholdSet, Finset.mem_filter, Finset.mem_univ, true_and]
      change fiberLayerMeanMoment (Finset.univ : Finset D.X) d' s / 2 ≤ d' x ^ s ↔
          (D.d x : ℝ) ^ s ≤ (2 * (Fintype.card D.X : ℝ)) / D.singularNegativeMoment s
      rw [fiberLayerMeanMoment, hmoment_s]
      simpa [d'] using threshold_condition_iff D s x hcard hmoment_pos
    have hcount' :
        (((Finset.univ.filter
            (fun x => (D.d x : ℝ) ^ s ≤
              (2 * (Fintype.card D.X : ℝ)) / D.singularNegativeMoment s)).card : ℝ)) ≥
          (D.singularNegativeMoment s) ^ 2 / (4 * D.singularNegativeMoment (2 * s)) := by
      simpa [hthreshold, hmoment_s, hmoment_s2] using hcount
    have hdiv :
        (D.singularNegativeMoment s ^ 2 / (4 * D.singularNegativeMoment (2 * s))) /
            (Fintype.card D.X : ℝ) ≤
          (((Finset.univ.filter
              (fun x => (D.d x : ℝ) ^ s ≤
                (2 * (Fintype.card D.X : ℝ)) / D.singularNegativeMoment s)).card : ℝ) /
            (Fintype.card D.X : ℝ)) := by
      exact (div_le_div_iff_of_pos_right hcard).2 hcount'
    simpa [ge_iff_le, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hdiv

end

end Omega.OperatorAlgebra

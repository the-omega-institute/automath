import Omega.OperatorAlgebra.FoldConditionalExpectationSingularSpectrum
import Omega.OperatorAlgebra.FoldReynoldsRiskConvex
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators
open Omega.OperatorAlgebra
open Omega.OperatorAlgebra.FoldFiberMultiplicity

noncomputable section

/-- The coarse `L²` energy obtained by projecting each fiber to its Reynolds average. -/
def conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) : ℝ :=
  ∑ x, reynoldsRisk (Finset.univ : Finset (Fin (D.d x))) (fun i => f ⟨x, i⟩)

/-- The fine `L²` energy before quotienting along the fibers. -/
def conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) : ℝ :=
  ∑ x, originalRisk (Finset.univ : Finset (Fin (D.d x))) (fun i => f ⟨x, i⟩)

/-- The per-fiber hidden-channel energy lost by quotienting. -/
def conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) (x : D.X) : ℝ :=
  originalRisk (Finset.univ : Finset (Fin (D.d x))) (fun i => f ⟨x, i⟩) -
    reynoldsRisk (Finset.univ : Finset (Fin (D.d x))) (fun i => f ⟨x, i⟩)

/-- All hidden channels vanish exactly when every per-fiber gap is zero. -/
def conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelsVanish
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) : Prop :=
  ∀ x, conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap D f x = 0

/-- Fiberwise constancy is modeled by equality with the conditional expectation on each fiber. -/
def conclusion_quotient_l2_equality_hidden_channels_vanish_fiberwiseConstancy
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) : Prop :=
  ∀ xi, f xi = D.conditionalExpectation f xi.1

/-- Membership in the projection image is the existence of a factorization through the base. -/
def conclusion_quotient_l2_equality_hidden_channels_vanish_inProjectionImage
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) : Prop :=
  ∃ g : D.X → ℝ, ∀ xi, f xi = g xi.1

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap_nonneg
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) (x : D.X) :
    0 ≤ conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap D f x := by
  unfold conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap
  have hs : (Finset.univ : Finset (Fin (D.d x))).Nonempty := by
    refine ⟨⟨0, D.d_pos x⟩, by simp⟩
  have hmono :=
    (paper_op_algebra_fold_reynolds_risk_convex
      (s := (Finset.univ : Finset (Fin (D.d x)))) hs (f := fun i => f ⟨x, i⟩)).1
  exact sub_nonneg.mpr hmono

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq_nonneg
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) :
    0 ≤ conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq D f := by
  unfold conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq
  refine Finset.sum_nonneg fun x _ => by
    unfold reynoldsRisk reynoldsAverage
    positivity

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq_nonneg
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) :
    0 ≤ conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq D f := by
  unfold conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq
  refine Finset.sum_nonneg fun x _ => by
    unfold originalRisk
    positivity

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq_le_fineL2Sq
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) :
    conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq D f ≤
      conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq D f := by
  unfold conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq
    conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq
  refine Finset.sum_le_sum fun x _ => ?_
  have hs : (Finset.univ : Finset (Fin (D.d x))).Nonempty := by
    refine ⟨⟨0, D.d_pos x⟩, by simp⟩
  exact
    (paper_op_algebra_fold_reynolds_risk_convex
      (s := (Finset.univ : Finset (Fin (D.d x)))) hs (f := fun i => f ⟨x, i⟩)).1

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_sum_hiddenChannelGap
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) :
    (∑ x,
        conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap D f x) =
      conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq D f -
        conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq D f := by
  unfold conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap
    conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq
    conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq
  rw [Finset.sum_sub_distrib]

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap_zero_iff_fiberwise
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) (x : D.X) :
    conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap D f x = 0 ↔
      ∀ i : Fin (D.d x), f ⟨x, i⟩ = D.conditionalExpectation f x := by
  have hs : (Finset.univ : Finset (Fin (D.d x))).Nonempty := by
    refine ⟨⟨0, D.d_pos x⟩, by simp⟩
  have hiff :=
    equalityIffFiberwiseConstant_proof
      (s := (Finset.univ : Finset (Fin (D.d x)))) hs (f := fun i => f ⟨x, i⟩)
  constructor
  · intro hgap i
    have heq :
        reynoldsRisk (Finset.univ : Finset (Fin (D.d x))) (fun j => f ⟨x, j⟩) =
          originalRisk (Finset.univ : Finset (Fin (D.d x))) (fun j => f ⟨x, j⟩) := by
      unfold conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap at hgap
      linarith
    have hconst := hiff.mp heq i (by simp)
    simpa [FoldFiberMultiplicity.conditionalExpectation, OperatorAlgebra.conditionalExpectation,
      reynoldsAverage] using
      hconst
  · intro hconst
    have hconst' :
        ∀ i ∈ (Finset.univ : Finset (Fin (D.d x))),
          f ⟨x, i⟩ = reynoldsAverage (Finset.univ : Finset (Fin (D.d x))) (fun j => f ⟨x, j⟩) := by
      intro i hi
      simpa [FoldFiberMultiplicity.conditionalExpectation, OperatorAlgebra.conditionalExpectation,
        reynoldsAverage]
        using hconst i
    have heq :
        reynoldsRisk (Finset.univ : Finset (Fin (D.d x))) (fun j => f ⟨x, j⟩) =
          originalRisk (Finset.univ : Finset (Fin (D.d x))) (fun j => f ⟨x, j⟩) :=
      hiff.mpr hconst'
    unfold conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap
    linarith

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelsVanish_iff_fiberwiseConstancy
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) :
    conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelsVanish D f ↔
      conclusion_quotient_l2_equality_hidden_channels_vanish_fiberwiseConstancy D f := by
  constructor
  · intro h xi
    exact
      (conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap_zero_iff_fiberwise
        D f xi.1).mp (h xi.1) xi.2
  · intro h x
    exact
      (conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap_zero_iff_fiberwise
        D f x).mpr (fun i => h ⟨x, i⟩)

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_conditionalExpectation_of_image
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) (g : D.X → ℝ)
    (hg : ∀ xi, f xi = g xi.1) (x : D.X) :
    D.conditionalExpectation f x = g x := by
  have hd : (D.d x : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.d_pos x)
  unfold FoldFiberMultiplicity.conditionalExpectation
  calc
    (∑ i : Fin (D.d x), f ⟨x, i⟩) / (D.d x : ℝ)
        = (∑ i : Fin (D.d x), g x) / (D.d x : ℝ) := by
            refine congrArg (fun z : ℝ => z / (D.d x : ℝ)) ?_
            simp [hg]
    _ = g x := by
          simp [hd]

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_fiberwiseConstancy_iff_inProjectionImage
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) :
    conclusion_quotient_l2_equality_hidden_channels_vanish_fiberwiseConstancy D f ↔
      conclusion_quotient_l2_equality_hidden_channels_vanish_inProjectionImage D f := by
  constructor
  · intro h
    refine ⟨D.conditionalExpectation f, ?_⟩
    intro xi
    exact h xi
  · rintro ⟨g, hg⟩ xi
    calc
      f xi = g xi.1 := hg xi
      _ = D.conditionalExpectation f xi.1 := by
            symm
            exact
              conclusion_quotient_l2_equality_hidden_channels_vanish_conditionalExpectation_of_image
                D f g hg xi.1

lemma conclusion_quotient_l2_equality_hidden_channels_vanish_global_sq_eq_iff_hiddenChannelsVanish
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) :
    conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq D f =
      conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq D f ↔
        conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelsVanish D f := by
  constructor
  · intro heq
    have hsum0 :
        (∑ x,
            conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap D f x) = 0 := by
      rw [conclusion_quotient_l2_equality_hidden_channels_vanish_sum_hiddenChannelGap D f]
      linarith
    intro x
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ =>
          conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap_nonneg D f y)).mp
        hsum0 x (by simp)
  · intro hvanish
    have hsum0 :
        (∑ x,
            conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelGap D f x) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      exact hvanish x
    rw [conclusion_quotient_l2_equality_hidden_channels_vanish_sum_hiddenChannelGap D f] at hsum0
    linarith

/-- Paper label: `thm:conclusion-quotient-l2-equality-hidden-channels-vanish`. In the finite
fiber model, quotienting replaces each fiber by its conditional expectation, the global `L²` norm
cannot increase, and equality occurs exactly when the hidden per-fiber channels vanish, equivalently
when the function is fiberwise constant and therefore lies in the projection image. -/
theorem paper_conclusion_quotient_l2_equality_hidden_channels_vanish
    (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) :
    Real.sqrt (conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq D f) ≤
      Real.sqrt (conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq D f) ∧
      (Real.sqrt (conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq D f) =
          Real.sqrt (conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq D f) ↔
        conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelsVanish D f) ∧
      (conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelsVanish D f ↔
        conclusion_quotient_l2_equality_hidden_channels_vanish_fiberwiseConstancy D f) ∧
      (conclusion_quotient_l2_equality_hidden_channels_vanish_fiberwiseConstancy D f ↔
        conclusion_quotient_l2_equality_hidden_channels_vanish_inProjectionImage D f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Real.sqrt_le_sqrt
      (conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq_le_fineL2Sq D f)
  · constructor
    · intro heq
      have hsq := congrArg (fun t : ℝ => t ^ 2) heq
      simp [Real.sq_sqrt,
        conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq_nonneg,
        conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq_nonneg] at hsq
      exact
        (conclusion_quotient_l2_equality_hidden_channels_vanish_global_sq_eq_iff_hiddenChannelsVanish
          D f).mp hsq
    · intro hvanish
      have hsq :
          conclusion_quotient_l2_equality_hidden_channels_vanish_coarseL2Sq D f =
            conclusion_quotient_l2_equality_hidden_channels_vanish_fineL2Sq D f :=
        (conclusion_quotient_l2_equality_hidden_channels_vanish_global_sq_eq_iff_hiddenChannelsVanish
          D f).mpr hvanish
      exact congrArg Real.sqrt hsq
  · exact
      conclusion_quotient_l2_equality_hidden_channels_vanish_hiddenChannelsVanish_iff_fiberwiseConstancy
        D f
  · exact
      conclusion_quotient_l2_equality_hidden_channels_vanish_fiberwiseConstancy_iff_inProjectionImage
        D f

end

end Omega.Conclusion

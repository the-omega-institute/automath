import Omega.OperatorAlgebra.FoldConditionalExpectation

open scoped BigOperators

namespace Omega.OperatorAlgebra

open FoldConditionalExpectationData

namespace FoldConditionalExpectationData

/-- Label-prefixed global mean for the finite uniform fold model. -/
def finite_condexp_variance_decomposition_weightedMean
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) : ℚ :=
  (∑ a : D.Ω, f a) / Fintype.card D.Ω

/-- Label-prefixed squared `L^2` norm for the finite uniform fold model. -/
def finite_condexp_variance_decomposition_l2NormSq
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) : ℚ :=
  ∑ a : D.Ω, f a * f a

/-- Label-prefixed finite variance around the global mean. -/
def finite_condexp_variance_decomposition_variance
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) : ℚ :=
  D.finite_condexp_variance_decomposition_l2NormSq
    (fun a => f a - D.finite_condexp_variance_decomposition_weightedMean f)

/-- Label-prefixed fiber dissipation, i.e. the squared residual from the fold average. -/
def finite_condexp_variance_decomposition_fiberDissipation
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) : ℚ :=
  D.finite_condexp_variance_decomposition_l2NormSq
    (fun a => f a - D.foldExpectation f a)

lemma finite_condexp_variance_decomposition_l2NormSq_nonneg
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) :
    0 ≤ D.finite_condexp_variance_decomposition_l2NormSq f := by
  classical
  simp [finite_condexp_variance_decomposition_l2NormSq]
  exact Finset.sum_nonneg fun a _ha => by
    simpa using mul_self_nonneg (f a)

lemma finite_condexp_variance_decomposition_fiber_residual_sum
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) (x : D.X) :
    Finset.sum (D.fiber x) (fun a => f a - D.foldExpectation f a) = 0 := by
  classical
  set S : ℚ := Finset.sum (D.fiber x) f
  set M : ℚ := (D.fiberCard x : ℚ)
  have hM : M ≠ 0 := by
    simpa [M] using (show (D.fiberCard x : ℚ) ≠ 0 by
      exact_mod_cast Nat.ne_of_gt (D.fiberCard_pos x))
  calc
    Finset.sum (D.fiber x) (fun a => f a - D.foldExpectation f a)
        = Finset.sum (D.fiber x) (fun a => f a - S / M) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            have hax : D.fold a = x := by
              simpa [FoldConditionalExpectationData.fiber] using ha
            simp [FoldConditionalExpectationData.foldExpectation, S, M, hax]
    _ = S - (S / M) * M := by
          simp [S, M, FoldConditionalExpectationData.fiberCard, Finset.sum_sub_distrib,
            Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = 0 := by
          field_simp [hM]
          ring

lemma finite_condexp_variance_decomposition_sum_foldExpectation
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) :
    (∑ a : D.Ω, D.foldExpectation f a) = ∑ a : D.Ω, f a := by
  classical
  have hres :
      (∑ a : D.Ω, (f a - D.foldExpectation f a)) = 0 := by
    calc
      (∑ a : D.Ω, (f a - D.foldExpectation f a))
          = ∑ x : D.X,
              Finset.sum (D.fiber x) (fun a => f a - D.foldExpectation f a) := by
              symm
              simpa [FoldConditionalExpectationData.fiber] using
                (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
                  (g := D.fold) (h := fun _ _ => by simp)
                  (f := fun a => f a - D.foldExpectation f a))
      _ = 0 := by
            simp [D.finite_condexp_variance_decomposition_fiber_residual_sum f]
  have hsplit :
      (∑ a : D.Ω, (f a - D.foldExpectation f a)) =
        (∑ a : D.Ω, f a) - ∑ a : D.Ω, D.foldExpectation f a := by
    simp [Finset.sum_sub_distrib]
  linarith

lemma finite_condexp_variance_decomposition_mean_foldExpectation
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) :
    D.finite_condexp_variance_decomposition_weightedMean (D.foldExpectation f) =
      D.finite_condexp_variance_decomposition_weightedMean f := by
  simp [finite_condexp_variance_decomposition_weightedMean,
    D.finite_condexp_variance_decomposition_sum_foldExpectation f]

lemma finite_condexp_variance_decomposition_foldExpectation_sub_const
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) (c : ℚ) :
    D.foldExpectation (fun a => f a - c) = fun a => D.foldExpectation f a - c := by
  classical
  funext a
  have hcard : ((D.fiber (D.fold a)).card : ℚ) ≠ 0 := by
    simpa [FoldConditionalExpectationData.fiberCard] using
      (show (D.fiberCard (D.fold a) : ℚ) ≠ 0 by
        exact_mod_cast Nat.ne_of_gt (D.fiberCard_pos (D.fold a)))
  simp [FoldConditionalExpectationData.foldExpectation, FoldConditionalExpectationData.fiberCard,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard]

lemma finite_condexp_variance_decomposition_orthogonal
    (D : FoldConditionalExpectationData) (B f : D.Ω → ℚ) (hB : D.fiberInvariant B) :
    (∑ a : D.Ω, B a * (f a - D.foldExpectation f a)) = 0 := by
  classical
  calc
    (∑ a : D.Ω, B a * (f a - D.foldExpectation f a))
        = ∑ x : D.X,
            Finset.sum (D.fiber x) (fun a => B a * (f a - D.foldExpectation f a)) := by
            symm
            simpa [FoldConditionalExpectationData.fiber] using
              (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
                (g := D.fold) (h := fun _ _ => by simp)
                (f := fun a => B a * (f a - D.foldExpectation f a)))
    _ = ∑ x : D.X,
          B (Classical.choose (D.fiber_nonempty x)) *
            Finset.sum (D.fiber x) (fun a => f a - D.foldExpectation f a) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          let b : D.Ω := Classical.choose (D.fiber_nonempty x)
          have hb : b ∈ D.fiber x := Classical.choose_spec (D.fiber_nonempty x)
          calc
            Finset.sum (D.fiber x) (fun a => B a * (f a - D.foldExpectation f a))
                = Finset.sum (D.fiber x)
                    (fun a => B b * (f a - D.foldExpectation f a)) := by
                    refine Finset.sum_congr rfl ?_
                    intro a ha
                    have hax : D.fold a = x := by
                      simpa [FoldConditionalExpectationData.fiber] using ha
                    have hbx : D.fold b = x := by
                      simpa [FoldConditionalExpectationData.fiber] using hb
                    rw [hB a b (hax.trans hbx.symm)]
            _ = B b * Finset.sum (D.fiber x)
                    (fun a => f a - D.foldExpectation f a) := by
                  rw [Finset.mul_sum]
    _ = 0 := by
          simp [D.finite_condexp_variance_decomposition_fiber_residual_sum f]

lemma finite_condexp_variance_decomposition_l2_pythagoras
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) :
    D.finite_condexp_variance_decomposition_l2NormSq f =
      D.finite_condexp_variance_decomposition_l2NormSq (D.foldExpectation f) +
        D.finite_condexp_variance_decomposition_fiberDissipation f := by
  classical
  have horth :
      (∑ a : D.Ω, D.foldExpectation f a * (f a - D.foldExpectation f a)) = 0 :=
    D.finite_condexp_variance_decomposition_orthogonal (D.foldExpectation f) f
      (D.foldExpectation_fiberInvariant f)
  simp [finite_condexp_variance_decomposition_l2NormSq,
    finite_condexp_variance_decomposition_fiberDissipation]
  calc
    (∑ a : D.Ω, f a * f a)
        =
          Finset.sum Finset.univ (fun a : D.Ω =>
            D.foldExpectation f a * D.foldExpectation f a +
              (f a - D.foldExpectation f a) * (f a - D.foldExpectation f a) +
              2 * (D.foldExpectation f a * (f a - D.foldExpectation f a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            ring
    _ =
        (∑ a : D.Ω, D.foldExpectation f a * D.foldExpectation f a) +
          (∑ a : D.Ω, (f a - D.foldExpectation f a) * (f a - D.foldExpectation f a)) +
            2 * (∑ a : D.Ω, D.foldExpectation f a * (f a - D.foldExpectation f a)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ =
        (∑ a : D.Ω, D.foldExpectation f a * D.foldExpectation f a) +
          ∑ a : D.Ω, (f a - D.foldExpectation f a) * (f a - D.foldExpectation f a) := by
          rw [horth]
          ring

/-- The finite conditional-expectation variance-decomposition statement. -/
def finite_condexp_variance_decomposition_statement
    (D : FoldConditionalExpectationData) : Prop :=
  ∀ f : D.Ω → ℚ,
    D.finite_condexp_variance_decomposition_fiberDissipation f =
        D.finite_condexp_variance_decomposition_l2NormSq
          (fun a => f a - D.foldExpectation f a) ∧
      D.finite_condexp_variance_decomposition_variance f =
        D.finite_condexp_variance_decomposition_variance (D.foldExpectation f) +
          D.finite_condexp_variance_decomposition_fiberDissipation f ∧
      D.finite_condexp_variance_decomposition_fiberDissipation (D.foldExpectation f) = 0 ∧
      D.finite_condexp_variance_decomposition_fiberDissipation (D.foldExpectation f) ≤
      D.finite_condexp_variance_decomposition_fiberDissipation f

end FoldConditionalExpectationData

/-- Paper label: `cor:finite-condexp-variance-decomposition`. -/
theorem paper_finite_condexp_variance_decomposition (D : FoldConditionalExpectationData) :
    finite_condexp_variance_decomposition_statement D := by
  classical
  intro f
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have hpy :=
      D.finite_condexp_variance_decomposition_l2_pythagoras
        (fun a => f a - D.finite_condexp_variance_decomposition_weightedMean f)
    have hmean :
        D.finite_condexp_variance_decomposition_weightedMean (D.foldExpectation f) =
          D.finite_condexp_variance_decomposition_weightedMean f :=
      D.finite_condexp_variance_decomposition_mean_foldExpectation f
    simpa [finite_condexp_variance_decomposition_variance,
      finite_condexp_variance_decomposition_fiberDissipation,
      D.finite_condexp_variance_decomposition_foldExpectation_sub_const
        f (D.finite_condexp_variance_decomposition_weightedMean f),
      hmean] using hpy
  · simp [finite_condexp_variance_decomposition_fiberDissipation,
      finite_condexp_variance_decomposition_l2NormSq, D.foldExpectation_idempotent f]
  · rw [show D.finite_condexp_variance_decomposition_fiberDissipation
        (D.foldExpectation f) = 0 by
        simp [finite_condexp_variance_decomposition_fiberDissipation,
          finite_condexp_variance_decomposition_l2NormSq, D.foldExpectation_idempotent f]]
    exact D.finite_condexp_variance_decomposition_l2NormSq_nonneg
      (fun a => f a - D.foldExpectation f a)

end Omega.OperatorAlgebra

import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The `21` visible fibers of the window-`6` coarse space, split by sizes
`8 × 2`, `4 × 3`, and `9 × 4`. -/
abbrev conclusion_window6_reynolds_average_zero_mode_projector_fiber :=
  Sum (Fin 8) (Sum (Fin 4) (Fin 9))

/-- The fiber cardinality `d(w)`. -/
def conclusion_window6_reynolds_average_zero_mode_projector_fiberCard :
    conclusion_window6_reynolds_average_zero_mode_projector_fiber → ℕ
  | .inl _ => 2
  | .inr (.inl _) => 3
  | .inr (.inr _) => 4

/-- The `64` microstates, organized fiberwise. -/
abbrev conclusion_window6_reynolds_average_zero_mode_projector_microstate :=
  Σ w : conclusion_window6_reynolds_average_zero_mode_projector_fiber,
    Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w)

/-- Fiberwise visible observables. -/
abbrev conclusion_window6_reynolds_average_zero_mode_projector_visibleObservable :=
  conclusion_window6_reynolds_average_zero_mode_projector_fiber → ℚ

/-- Micro-observables on `Ω₆`. -/
abbrev conclusion_window6_reynolds_average_zero_mode_projector_observable :=
  conclusion_window6_reynolds_average_zero_mode_projector_microstate → ℚ

/-- Lift a visible observable to a micro-observable by pulling back along the fiber projection. -/
def conclusion_window6_reynolds_average_zero_mode_projector_visibleLift
    (φ : conclusion_window6_reynolds_average_zero_mode_projector_visibleObservable) :
    conclusion_window6_reynolds_average_zero_mode_projector_observable
  := fun x => φ x.1

/-- The Reynolds operator, written directly as the fiberwise uniform average. -/
def conclusion_window6_reynolds_average_zero_mode_projector_reynolds
    (f : conclusion_window6_reynolds_average_zero_mode_projector_observable) :
    conclusion_window6_reynolds_average_zero_mode_projector_observable
  | ⟨w, _n⟩ =>
      (∑ m : Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w), f ⟨w, m⟩) /
        (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w : ℚ)

/-- Fiberwise constancy is the visible subspace condition. -/
def conclusion_window6_reynolds_average_zero_mode_projector_fiberwiseConstant
    (f : conclusion_window6_reynolds_average_zero_mode_projector_observable) : Prop :=
  ∀ w
    (n m : Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w)),
      f ⟨w, n⟩ = f ⟨w, m⟩

/-- The pushed-forward counting measure `p₆(w) = d(w) / 64`. -/
def conclusion_window6_reynolds_average_zero_mode_projector_fiberWeight
    (w : conclusion_window6_reynolds_average_zero_mode_projector_fiber) : ℚ :=
  (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w : ℚ) / 64

/-- The normalized microstate `L²` norm squared. -/
def conclusion_window6_reynolds_average_zero_mode_projector_microNormSq
    (f : conclusion_window6_reynolds_average_zero_mode_projector_observable) : ℚ :=
  (∑ x : conclusion_window6_reynolds_average_zero_mode_projector_microstate, (f x) ^ 2) / 64

/-- The corresponding weighted visible norm squared. -/
def conclusion_window6_reynolds_average_zero_mode_projector_visibleNormSq
    (φ : conclusion_window6_reynolds_average_zero_mode_projector_visibleObservable) : ℚ :=
  (∑ w : conclusion_window6_reynolds_average_zero_mode_projector_fiber,
      (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w : ℚ) * (φ w) ^ 2) / 64

/-- The cubic spectral polynomial cutting out the zero eigenspace of the fiber Laplacian. -/
def conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial (t : ℚ) : ℚ :=
  -((1 : ℚ) / 24) * (t - 2) * (t - 3) * (t - 4)

/-- Fiberwise polynomial functional calculus for the complete-graph Laplacian: constants are the
`0`-eigenspace and the orthogonal complement has eigenvalue `d(w)`. -/
def conclusion_window6_reynolds_average_zero_mode_projector_zeroModeProjector
    (f : conclusion_window6_reynolds_average_zero_mode_projector_observable) :
    conclusion_window6_reynolds_average_zero_mode_projector_observable
  | ⟨w, n⟩ =>
      let avg := conclusion_window6_reynolds_average_zero_mode_projector_reynolds f ⟨w, n⟩
      avg +
        conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial
            (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w) *
          (f ⟨w, n⟩ - avg)

lemma conclusion_window6_reynolds_average_zero_mode_projector_fiberCard_ne_zero
    (w : conclusion_window6_reynolds_average_zero_mode_projector_fiber) :
    (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w : ℚ) ≠ 0 := by
  cases w with
  | inl i =>
      norm_num [conclusion_window6_reynolds_average_zero_mode_projector_fiberCard]
  | inr w =>
      cases w with
      | inl j =>
          norm_num [conclusion_window6_reynolds_average_zero_mode_projector_fiberCard]
      | inr k =>
          norm_num [conclusion_window6_reynolds_average_zero_mode_projector_fiberCard]

lemma conclusion_window6_reynolds_average_zero_mode_projector_reynolds_eq_visibleLift
    (f : conclusion_window6_reynolds_average_zero_mode_projector_observable) :
    ∃ φ : conclusion_window6_reynolds_average_zero_mode_projector_visibleObservable,
      conclusion_window6_reynolds_average_zero_mode_projector_reynolds f =
        conclusion_window6_reynolds_average_zero_mode_projector_visibleLift φ := by
  refine ⟨fun w =>
    (∑ m : Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w), f ⟨w, m⟩) /
      (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w : ℚ), ?_⟩
  funext x
  rcases x with ⟨w, n⟩
  rfl

lemma conclusion_window6_reynolds_average_zero_mode_projector_reynolds_eq_self_iff
    (f : conclusion_window6_reynolds_average_zero_mode_projector_observable) :
    conclusion_window6_reynolds_average_zero_mode_projector_reynolds f = f ↔
      conclusion_window6_reynolds_average_zero_mode_projector_fiberwiseConstant f := by
  constructor
  · intro h w n m
    have hn := congrFun h ⟨w, n⟩
    have hm := congrFun h ⟨w, m⟩
    have havg :
        conclusion_window6_reynolds_average_zero_mode_projector_reynolds f ⟨w, n⟩ =
          conclusion_window6_reynolds_average_zero_mode_projector_reynolds f ⟨w, m⟩ := by
      simp [conclusion_window6_reynolds_average_zero_mode_projector_reynolds]
    exact hn.symm.trans (havg.trans hm)
  · intro hconst
    funext x
    rcases x with ⟨w, n⟩
    have hsum :
        (∑ m : Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w), f ⟨w, m⟩) =
          ∑ _ : Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w), f ⟨w, n⟩ := by
      classical
      exact Finset.sum_congr rfl (fun m _ => hconst w m n)
    have hcard :
        (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w : ℚ) ≠ 0 :=
      conclusion_window6_reynolds_average_zero_mode_projector_fiberCard_ne_zero w
    rw [conclusion_window6_reynolds_average_zero_mode_projector_reynolds, hsum]
    field_simp [hcard]
    simp

lemma conclusion_window6_reynolds_average_zero_mode_projector_visible_norm_formula
    (φ : conclusion_window6_reynolds_average_zero_mode_projector_visibleObservable) :
    conclusion_window6_reynolds_average_zero_mode_projector_visibleNormSq φ =
      ∑ w : conclusion_window6_reynolds_average_zero_mode_projector_fiber,
        conclusion_window6_reynolds_average_zero_mode_projector_fiberWeight w * (φ w) ^ 2 := by
  unfold conclusion_window6_reynolds_average_zero_mode_projector_visibleNormSq
    conclusion_window6_reynolds_average_zero_mode_projector_fiberWeight
  rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro w hw
  ring

lemma conclusion_window6_reynolds_average_zero_mode_projector_micro_norm_visibleLift
    (φ : conclusion_window6_reynolds_average_zero_mode_projector_visibleObservable) :
    conclusion_window6_reynolds_average_zero_mode_projector_microNormSq
        (conclusion_window6_reynolds_average_zero_mode_projector_visibleLift φ) =
      conclusion_window6_reynolds_average_zero_mode_projector_visibleNormSq φ := by
  unfold conclusion_window6_reynolds_average_zero_mode_projector_microNormSq
    conclusion_window6_reynolds_average_zero_mode_projector_visibleNormSq
    conclusion_window6_reynolds_average_zero_mode_projector_visibleLift
  change
      (∑ x : Σ w : conclusion_window6_reynolds_average_zero_mode_projector_fiber,
          Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w),
          (fun w _ => φ w ^ 2) x.1 x.2) /
        64 =
      (∑ w : conclusion_window6_reynolds_average_zero_mode_projector_fiber,
          (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w : ℚ) * (φ w) ^ 2) /
        64
  rw [show
      (∑ x : Σ w : conclusion_window6_reynolds_average_zero_mode_projector_fiber,
          Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w),
          (fun w _ => φ w ^ 2) x.1 x.2) =
        Finset.sum
          (Finset.univ.sigma
            (fun w : conclusion_window6_reynolds_average_zero_mode_projector_fiber =>
              (Finset.univ :
                Finset (Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w)))))
          (fun x => (fun w _ => φ w ^ 2) x.1 x.2) by
        rfl]
  rw [Finset.sum_sigma]
  simp

lemma conclusion_window6_reynolds_average_zero_mode_projector_zeroMode_eq_reynolds
    (f : conclusion_window6_reynolds_average_zero_mode_projector_observable) :
    conclusion_window6_reynolds_average_zero_mode_projector_zeroModeProjector f =
      conclusion_window6_reynolds_average_zero_mode_projector_reynolds f := by
  funext x
  rcases x with ⟨w, n⟩
  cases w with
  | inl i =>
      simp [conclusion_window6_reynolds_average_zero_mode_projector_zeroModeProjector,
        conclusion_window6_reynolds_average_zero_mode_projector_reynolds,
        conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial,
        conclusion_window6_reynolds_average_zero_mode_projector_fiberCard]
  | inr w =>
      cases w with
      | inl j =>
          simp [conclusion_window6_reynolds_average_zero_mode_projector_zeroModeProjector,
            conclusion_window6_reynolds_average_zero_mode_projector_reynolds,
            conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial,
            conclusion_window6_reynolds_average_zero_mode_projector_fiberCard]
      | inr k =>
          simp [conclusion_window6_reynolds_average_zero_mode_projector_zeroModeProjector,
            conclusion_window6_reynolds_average_zero_mode_projector_reynolds,
            conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial,
            conclusion_window6_reynolds_average_zero_mode_projector_fiberCard]

/-- Paper label: `prop:conclusion-window6-reynolds-average-zero-mode-projector`. The window-`6`
Reynolds operator is exactly the fiberwise uniform average on the `8 × 2`, `4 × 3`, and `9 × 4`
fibers, its image is the visible `21`-dimensional subspace, the normalized microstate norm
descends to the weighted visible norm with weights `d(w) / 64`, and the same operator is the
zero-mode projector cut out by the cubic polynomial vanishing at `2`, `3`, and `4`. -/
theorem paper_conclusion_window6_reynolds_average_zero_mode_projector :
    Fintype.card conclusion_window6_reynolds_average_zero_mode_projector_fiber = 21 ∧
      Fintype.card conclusion_window6_reynolds_average_zero_mode_projector_microstate = 64 ∧
      (∀ f
        (w : conclusion_window6_reynolds_average_zero_mode_projector_fiber)
        (n : Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w)),
          conclusion_window6_reynolds_average_zero_mode_projector_reynolds f ⟨w, n⟩ =
            (∑ m : Fin (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w),
                f ⟨w, m⟩) /
              (conclusion_window6_reynolds_average_zero_mode_projector_fiberCard w : ℚ)) ∧
      (∀ f, ∃ φ : conclusion_window6_reynolds_average_zero_mode_projector_visibleObservable,
          conclusion_window6_reynolds_average_zero_mode_projector_reynolds f =
            conclusion_window6_reynolds_average_zero_mode_projector_visibleLift φ) ∧
      (∀ f,
          conclusion_window6_reynolds_average_zero_mode_projector_reynolds f = f ↔
            conclusion_window6_reynolds_average_zero_mode_projector_fiberwiseConstant f) ∧
      (∀ φ,
          conclusion_window6_reynolds_average_zero_mode_projector_microNormSq
              (conclusion_window6_reynolds_average_zero_mode_projector_visibleLift φ) =
            conclusion_window6_reynolds_average_zero_mode_projector_visibleNormSq φ ∧
          conclusion_window6_reynolds_average_zero_mode_projector_visibleNormSq φ =
            ∑ w : conclusion_window6_reynolds_average_zero_mode_projector_fiber,
              conclusion_window6_reynolds_average_zero_mode_projector_fiberWeight w * (φ w) ^ 2) ∧
      (∀ f,
          conclusion_window6_reynolds_average_zero_mode_projector_zeroModeProjector f =
            conclusion_window6_reynolds_average_zero_mode_projector_reynolds f) ∧
      conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial 0 = 1 ∧
      conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial 2 = 0 ∧
      conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial 3 = 0 ∧
      conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [conclusion_window6_reynolds_average_zero_mode_projector_fiber]
  · simp [conclusion_window6_reynolds_average_zero_mode_projector_microstate,
      conclusion_window6_reynolds_average_zero_mode_projector_fiber,
      conclusion_window6_reynolds_average_zero_mode_projector_fiberCard]
  · intro f w n
    rfl
  · intro f
    exact conclusion_window6_reynolds_average_zero_mode_projector_reynolds_eq_visibleLift f
  · intro f
    exact conclusion_window6_reynolds_average_zero_mode_projector_reynolds_eq_self_iff f
  · intro φ
    exact ⟨conclusion_window6_reynolds_average_zero_mode_projector_micro_norm_visibleLift φ,
      conclusion_window6_reynolds_average_zero_mode_projector_visible_norm_formula φ⟩
  · intro f
    exact conclusion_window6_reynolds_average_zero_mode_projector_zeroMode_eq_reynolds f
  · norm_num [conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial]
  · norm_num [conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial]
  · norm_num [conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial]
  · norm_num [conclusion_window6_reynolds_average_zero_mode_projector_spectralPolynomial]

end Omega.Conclusion

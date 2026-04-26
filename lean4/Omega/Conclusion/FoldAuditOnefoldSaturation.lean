import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Filter.Basic
import Omega.Conclusion.CycleRankSaturation

namespace Omega.Conclusion

open Filter

/-- Concrete finite data for the one-fold audit saturation package. The observation and
measurement idempotents are modeled as section-retraction factorizations through a common middle
space, and the normalized rank sequence is compared with the Fibonacci upper bound. -/
structure conclusion_fold_audit_onefold_saturation_data where
  observationDim : ℕ
  measurementDim : ℕ
  middleDim : ℕ
  observationRetraction : Fin middleDim → Fin observationDim
  observationSection : Fin observationDim → Fin middleDim
  measurementRetraction : Fin middleDim → Fin measurementDim
  measurementSection : Fin measurementDim → Fin middleDim
  observation_leftInverse :
    Function.LeftInverse observationRetraction observationSection
  measurement_leftInverse :
    Function.LeftInverse measurementRetraction measurementSection
  observation_fullRank : Function.Surjective observationSection
  measurement_fullRank : Function.Surjective measurementSection
  rankSeq : ℕ → ℕ
  rankSeq_upper : ∀ n, rankSeq n ≤ Nat.fib (n + 2)
  rankSeq_lower : ∀ n, Nat.fib (n + 2) ≤ rankSeq n

namespace conclusion_fold_audit_onefold_saturation_data

/-- The observation-side idempotent on the middle space. -/
def conclusion_fold_audit_onefold_saturation_observation_projector
    (h : conclusion_fold_audit_onefold_saturation_data) :
    Fin h.middleDim → Fin h.middleDim :=
  fun x => h.observationSection (h.observationRetraction x)

/-- The measurement-side idempotent on the middle space. -/
def conclusion_fold_audit_onefold_saturation_measurement_projector
    (h : conclusion_fold_audit_onefold_saturation_data) :
    Fin h.middleDim → Fin h.middleDim :=
  fun x => h.measurementSection (h.measurementRetraction x)

/-- Finite image-cardinality rank proxy for the projectors. -/
def conclusion_fold_audit_onefold_saturation_rank
    {α : Type} [Fintype α] [DecidableEq α] (f : α → α) : ℕ :=
  (Finset.univ.image f).card

/-- The normalized audit-rank sequence. -/
noncomputable def conclusion_fold_audit_onefold_saturation_normalized_rank
    (h : conclusion_fold_audit_onefold_saturation_data) (n : ℕ) : ℝ :=
  h.rankSeq n / Nat.fib (n + 2)

/-- Paper-facing statement: both factorized endomorphisms are idempotent, their finite ranks are
the section ranks, full rank forces both to be the identity on the middle space, hence the two
projectors agree, and the normalized rank sequence has positive liminf because it saturates the
Fibonacci upper bound. -/
def statement (h : conclusion_fold_audit_onefold_saturation_data) : Prop :=
  (∀ x,
      h.conclusion_fold_audit_onefold_saturation_observation_projector
          (h.conclusion_fold_audit_onefold_saturation_observation_projector x) =
        h.conclusion_fold_audit_onefold_saturation_observation_projector x) ∧
    (∀ x,
      h.conclusion_fold_audit_onefold_saturation_measurement_projector
          (h.conclusion_fold_audit_onefold_saturation_measurement_projector x) =
        h.conclusion_fold_audit_onefold_saturation_measurement_projector x) ∧
    conclusion_fold_audit_onefold_saturation_rank
        h.conclusion_fold_audit_onefold_saturation_observation_projector =
      h.observationDim ∧
    conclusion_fold_audit_onefold_saturation_rank
        h.conclusion_fold_audit_onefold_saturation_measurement_projector =
      h.measurementDim ∧
    h.conclusion_fold_audit_onefold_saturation_observation_projector = id ∧
    h.conclusion_fold_audit_onefold_saturation_measurement_projector = id ∧
    h.conclusion_fold_audit_onefold_saturation_observation_projector =
      h.conclusion_fold_audit_onefold_saturation_measurement_projector ∧
    (∀ n, h.rankSeq n = Nat.fib (n + 2)) ∧
    Omega.Conclusion.CycleRankSaturation.PositiveLiminf
      h.conclusion_fold_audit_onefold_saturation_normalized_rank

end conclusion_fold_audit_onefold_saturation_data

open conclusion_fold_audit_onefold_saturation_data

private lemma conclusion_fold_audit_onefold_saturation_observation_projector_image
    (h : conclusion_fold_audit_onefold_saturation_data) :
    Finset.image h.conclusion_fold_audit_onefold_saturation_observation_projector Finset.univ =
      Finset.image h.observationSection Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨h.observationRetraction y, rfl⟩
  · rintro ⟨i, -, rfl⟩
    refine ⟨h.observationSection i, ?_⟩
    rw [conclusion_fold_audit_onefold_saturation_observation_projector, h.observation_leftInverse i]

private lemma conclusion_fold_audit_onefold_saturation_measurement_projector_image
    (h : conclusion_fold_audit_onefold_saturation_data) :
    Finset.image h.conclusion_fold_audit_onefold_saturation_measurement_projector Finset.univ =
      Finset.image h.measurementSection Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨h.measurementRetraction y, rfl⟩
  · rintro ⟨i, -, rfl⟩
    refine ⟨h.measurementSection i, ?_⟩
    rw [conclusion_fold_audit_onefold_saturation_measurement_projector, h.measurement_leftInverse i]

private lemma conclusion_fold_audit_onefold_saturation_observation_rank
    (h : conclusion_fold_audit_onefold_saturation_data) :
    conclusion_fold_audit_onefold_saturation_rank
        h.conclusion_fold_audit_onefold_saturation_observation_projector =
      h.observationDim := by
  unfold conclusion_fold_audit_onefold_saturation_rank
  rw [conclusion_fold_audit_onefold_saturation_observation_projector_image]
  simpa using
    Finset.card_image_of_injective (s := Finset.univ) (f := h.observationSection)
      (Function.LeftInverse.injective h.observation_leftInverse)

private lemma conclusion_fold_audit_onefold_saturation_measurement_rank
    (h : conclusion_fold_audit_onefold_saturation_data) :
    conclusion_fold_audit_onefold_saturation_rank
        h.conclusion_fold_audit_onefold_saturation_measurement_projector =
      h.measurementDim := by
  unfold conclusion_fold_audit_onefold_saturation_rank
  rw [conclusion_fold_audit_onefold_saturation_measurement_projector_image]
  simpa using
    Finset.card_image_of_injective (s := Finset.univ) (f := h.measurementSection)
      (Function.LeftInverse.injective h.measurement_leftInverse)

private lemma conclusion_fold_audit_onefold_saturation_observation_idempotent
    (h : conclusion_fold_audit_onefold_saturation_data) :
    ∀ x,
      h.conclusion_fold_audit_onefold_saturation_observation_projector
          (h.conclusion_fold_audit_onefold_saturation_observation_projector x) =
        h.conclusion_fold_audit_onefold_saturation_observation_projector x := by
  intro x
  simp [conclusion_fold_audit_onefold_saturation_observation_projector,
    h.observation_leftInverse (h.observationRetraction x)]

private lemma conclusion_fold_audit_onefold_saturation_measurement_idempotent
    (h : conclusion_fold_audit_onefold_saturation_data) :
    ∀ x,
      h.conclusion_fold_audit_onefold_saturation_measurement_projector
          (h.conclusion_fold_audit_onefold_saturation_measurement_projector x) =
        h.conclusion_fold_audit_onefold_saturation_measurement_projector x := by
  intro x
  simp [conclusion_fold_audit_onefold_saturation_measurement_projector,
    h.measurement_leftInverse (h.measurementRetraction x)]

private lemma conclusion_fold_audit_onefold_saturation_observation_eq_id
    (h : conclusion_fold_audit_onefold_saturation_data) :
    h.conclusion_fold_audit_onefold_saturation_observation_projector = id := by
  funext x
  rcases h.observation_fullRank x with ⟨i, rfl⟩
  simp [conclusion_fold_audit_onefold_saturation_observation_projector, h.observation_leftInverse i]

private lemma conclusion_fold_audit_onefold_saturation_measurement_eq_id
    (h : conclusion_fold_audit_onefold_saturation_data) :
    h.conclusion_fold_audit_onefold_saturation_measurement_projector = id := by
  funext x
  rcases h.measurement_fullRank x with ⟨i, rfl⟩
  simp [conclusion_fold_audit_onefold_saturation_measurement_projector,
    h.measurement_leftInverse i]

private lemma conclusion_fold_audit_onefold_saturation_rank_eq_fib
    (h : conclusion_fold_audit_onefold_saturation_data) (n : ℕ) :
    h.rankSeq n = Nat.fib (n + 2) := by
  exact Nat.le_antisymm (h.rankSeq_upper n) (h.rankSeq_lower n)

private lemma conclusion_fold_audit_onefold_saturation_normalized_rank_eq_one
    (h : conclusion_fold_audit_onefold_saturation_data) (n : ℕ) :
    h.conclusion_fold_audit_onefold_saturation_normalized_rank n = 1 := by
  have hpos : 0 < Nat.fib (n + 2) := by
    exact Nat.fib_pos.2 (by omega)
  rw [conclusion_fold_audit_onefold_saturation_normalized_rank,
    conclusion_fold_audit_onefold_saturation_rank_eq_fib h n]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hpos))

private lemma conclusion_fold_audit_onefold_saturation_positive_liminf
    (h : conclusion_fold_audit_onefold_saturation_data) :
    Omega.Conclusion.CycleRankSaturation.PositiveLiminf
      h.conclusion_fold_audit_onefold_saturation_normalized_rank := by
  refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
  intro n
  rw [conclusion_fold_audit_onefold_saturation_normalized_rank_eq_one h n]

/-- Paper label: `thm:conclusion-fold-audit-onefold-saturation`. -/
theorem paper_conclusion_fold_audit_onefold_saturation
    (h : conclusion_fold_audit_onefold_saturation_data) : h.statement := by
  refine ⟨conclusion_fold_audit_onefold_saturation_observation_idempotent h,
    conclusion_fold_audit_onefold_saturation_measurement_idempotent h,
    conclusion_fold_audit_onefold_saturation_observation_rank h,
    conclusion_fold_audit_onefold_saturation_measurement_rank h,
    conclusion_fold_audit_onefold_saturation_observation_eq_id h,
    conclusion_fold_audit_onefold_saturation_measurement_eq_id h, ?_, ?_,
    conclusion_fold_audit_onefold_saturation_positive_liminf h⟩
  · rw [conclusion_fold_audit_onefold_saturation_observation_eq_id h,
      conclusion_fold_audit_onefold_saturation_measurement_eq_id h]
  · intro n
    exact conclusion_fold_audit_onefold_saturation_rank_eq_fib h n

end Omega.Conclusion

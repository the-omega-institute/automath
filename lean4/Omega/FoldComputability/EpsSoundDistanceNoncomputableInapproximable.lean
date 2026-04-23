import Mathlib.Tactic
import Omega.FoldComputability.EpsSoundDistanceHaltingSpectrum

namespace Omega.FoldComputability

noncomputable section

/-- Concrete data for the noncomputability and inapproximability of the halting-coded
`ε`-sound distance. The map `haltingTime` packages the `T(M, x)` parameter from the paper, and the
undecidability input is the nonexistence of pointwise deciders for `halts`. -/
structure fold_computability_eps_sound_distance_noncomputable_inapproximable_data where
  Code : Type
  halts : Code → Prop
  haltingTime : Code → Option ℕ
  halts_iff : ∀ c, halts c ↔ ∃ T, haltingTime c = some T
  halts_undecidable : ¬ Nonempty (∀ c, Decidable (halts c))

namespace fold_computability_eps_sound_distance_noncomputable_inapproximable_data

/-- The concrete halting-coded `ε`-sound distance attached to a code `c`. -/
def fold_computability_eps_sound_distance_noncomputable_inapproximable_distance
    (D : fold_computability_eps_sound_distance_noncomputable_inapproximable_data) (c : D.Code) :
    ℝ :=
  fold_computability_eps_sound_distance_halting_spectrum_epsSoundDistance
    (fold_computability_eps_sound_distance_halting_spectrum_haltingCode (D.haltingTime c))
    fold_computability_eps_sound_distance_halting_spectrum_constantOne

/-- An exact computer outputs the precise `ε`-sound distance on every input. -/
def no_exact_computer
    (D : fold_computability_eps_sound_distance_noncomputable_inapproximable_data) : Prop :=
  ¬ ∃ compute : D.Code → ℝ,
      ∀ c,
        compute c =
          D.fold_computability_eps_sound_distance_noncomputable_inapproximable_distance c

/-- A factor-two approximator must output `0` in the non-halting case and stay within the explicit
dyadic factor-two window in the halting case. -/
def no_factor_two_approximator
    (D : fold_computability_eps_sound_distance_noncomputable_inapproximable_data) : Prop :=
  ¬ ∃ approx : D.Code → ℚ,
      ∀ c,
        match D.haltingTime c with
        | none => approx c = 0
        | some T =>
            ((1 / 2 : ℚ) ^ (T + 1) ≤ approx c) ∧ approx c ≤ 2 * ((1 / 2 : ℚ) ^ T)

lemma fold_computability_eps_sound_distance_noncomputable_inapproximable_distance_eq
    (D : fold_computability_eps_sound_distance_noncomputable_inapproximable_data) (c : D.Code) :
    D.fold_computability_eps_sound_distance_noncomputable_inapproximable_distance c =
      match D.haltingTime c with
      | none => 0
      | some T => (1 / 2 : ℝ) ^ T := by
  unfold
    fold_computability_eps_sound_distance_noncomputable_inapproximable_distance
  simpa using
    (paper_fold_computability_eps_sound_distance_halting_spectrum
      (f := fun _ => false) (g := fun _ => false) (T := D.haltingTime c)).2

lemma fold_computability_eps_sound_distance_noncomputable_inapproximable_not_halts_iff
    (D : fold_computability_eps_sound_distance_noncomputable_inapproximable_data) (c : D.Code) :
    ¬ D.halts c ↔ D.haltingTime c = none := by
  constructor
  · intro hnot
    cases htime : D.haltingTime c with
    | none =>
        rfl
    | some T =>
        have hhalt : D.halts c := (D.halts_iff c).2 ⟨T, htime⟩
        exact False.elim (hnot hhalt)
  · intro hnone hhalt
    rcases (D.halts_iff c).1 hhalt with ⟨T, hT⟩
    rw [hnone] at hT
    simp at hT

end fold_computability_eps_sound_distance_noncomputable_inapproximable_data

/-- Paper label: `cor:fold-computability-eps-sound-distance-noncomputable-inapproximable`. The
halting-coded `ε`-sound distance is `0` exactly in the non-halting case and equals `2^{-T}` in the
halting case. Therefore any exact evaluator, and even any factor-two approximator with the paper's
`q = 0` convention in the non-halting case, would decide halting by a zero test. -/
theorem paper_fold_computability_eps_sound_distance_noncomputable_inapproximable
    (D : fold_computability_eps_sound_distance_noncomputable_inapproximable_data) :
    D.no_exact_computer ∧ D.no_factor_two_approximator := by
  refine ⟨?_, ?_⟩
  · intro hExact
    rcases hExact with ⟨compute, hcompute⟩
    apply D.halts_undecidable
    classical
    refine ⟨fun c => by
      by_cases hzero : compute c = 0
      · refine isFalse ?_
        intro hhalt
        rcases (D.halts_iff c).1 hhalt with ⟨T, hT⟩
        have hdist :
            D.fold_computability_eps_sound_distance_noncomputable_inapproximable_distance c =
              (1 / 2 : ℝ) ^ T := by
          simpa [hT] using
            D.fold_computability_eps_sound_distance_noncomputable_inapproximable_distance_eq c
        have hnonzero : compute c ≠ 0 := by
          rw [hcompute c, hdist]
          exact pow_ne_zero T (by norm_num : (1 / 2 : ℝ) ≠ 0)
        exact hnonzero hzero
      · refine isTrue ?_
        by_contra hnot
        have hnone : D.haltingTime c = none :=
          (D.fold_computability_eps_sound_distance_noncomputable_inapproximable_not_halts_iff c).1
            hnot
        have hdist :
            D.fold_computability_eps_sound_distance_noncomputable_inapproximable_distance c = 0 := by
          simpa [hnone] using
            D.fold_computability_eps_sound_distance_noncomputable_inapproximable_distance_eq c
        exact hzero (by rw [hcompute c, hdist])⟩
  · intro hApprox
    rcases hApprox with ⟨approx, hApprox⟩
    apply D.halts_undecidable
    classical
    refine ⟨fun c => by
      by_cases hzero : approx c = 0
      · refine isFalse ?_
        intro hhalt
        rcases (D.halts_iff c).1 hhalt with ⟨T, hT⟩
        have hbounds :
            ((1 / 2 : ℚ) ^ (T + 1) ≤ approx c) ∧ approx c ≤ 2 * ((1 / 2 : ℚ) ^ T) := by
          simpa [hT] using hApprox c
        have hpos : 0 < (1 / 2 : ℚ) ^ (T + 1) := by
          positivity
        have hnonzero : approx c ≠ 0 := ne_of_gt (lt_of_lt_of_le hpos hbounds.1)
        exact hnonzero hzero
      · refine isTrue ?_
        by_contra hnot
        have hnone : D.haltingTime c = none :=
          (D.fold_computability_eps_sound_distance_noncomputable_inapproximable_not_halts_iff c).1
            hnot
        have hzero' : approx c = 0 := by
          simpa [hnone] using hApprox c
        exact hzero hzero'⟩

end

end Omega.FoldComputability

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The indicator used to evaluate a Boolean readout on a measurable subset of `Bool`. -/
def dephys_eps_sound_dominates_tv_indicator (A : Finset Bool) (b : Bool) : ℝ :=
  if b ∈ A then 1 else 0

/-- Unnormalized mass that the readout `x` assigns to the measurable set `A`. -/
noncomputable def dephys_eps_sound_dominates_tv_eventMass {State : Type*} [Fintype State]
    (x : State → Bool) (A : Finset Bool) : ℝ :=
  ∑ ω : State, dephys_eps_sound_dominates_tv_indicator A (x ω)

/-- Normalized discrepancy on one measurable subset of `Bool`. -/
noncomputable def dephys_eps_sound_dominates_tv_setDiscrepancy {State : Type*} [Fintype State]
    (x y : State → Bool) (A : Finset Bool) : ℝ :=
  |dephys_eps_sound_dominates_tv_eventMass x A - dephys_eps_sound_dominates_tv_eventMass y A| /
    Fintype.card State

/-- Total variation as the supremum over measurable-set discrepancies. -/
noncomputable def dephys_eps_sound_dominates_tv_totalVariation {State : Type*} [Fintype State]
    (x y : State → Bool) : ℝ :=
  sSup (Set.range (dephys_eps_sound_dominates_tv_setDiscrepancy x y))

private lemma dephys_eps_sound_dominates_tv_indicator_nonneg (A : Finset Bool) (b : Bool) :
    0 ≤ dephys_eps_sound_dominates_tv_indicator A b := by
  by_cases hb : b ∈ A <;> simp [dephys_eps_sound_dominates_tv_indicator, hb]

private lemma dephys_eps_sound_dominates_tv_indicator_abs_sub_le_one (A : Finset Bool)
    (b₁ b₂ : Bool) :
    |dephys_eps_sound_dominates_tv_indicator A b₁ -
        dephys_eps_sound_dominates_tv_indicator A b₂| ≤ 1 := by
  by_cases hb₁ : b₁ ∈ A <;> by_cases hb₂ : b₂ ∈ A <;>
    simp [dephys_eps_sound_dominates_tv_indicator, hb₁, hb₂]

private lemma dephys_eps_sound_dominates_tv_indicator_abs_sub_eq_zero_of_eq (A : Finset Bool)
    {b₁ b₂ : Bool} (h : b₁ = b₂) :
    |dephys_eps_sound_dominates_tv_indicator A b₁ -
        dephys_eps_sound_dominates_tv_indicator A b₂| = 0 := by
  subst h
  simp

private lemma dephys_eps_sound_dominates_tv_pointwise_bad_bound {State : Type*}
    [Fintype State] [DecidableEq State] (x y : State → Bool) (bad : Finset State)
    (hagree : ∀ ω, ω ∉ bad → x ω = y ω) (A : Finset Bool) :
    ∀ ω : State,
      |dephys_eps_sound_dominates_tv_indicator A (x ω) -
          dephys_eps_sound_dominates_tv_indicator A (y ω)| ≤
        if ω ∈ bad then 1 else 0 := by
  classical
  intro ω
  by_cases hω : ω ∈ bad
  · simpa [hω] using
      dephys_eps_sound_dominates_tv_indicator_abs_sub_le_one A (x ω) (y ω)
  · have hxy : x ω = y ω := hagree ω hω
    rw [if_neg hω]
    exact le_of_eq
      (dephys_eps_sound_dominates_tv_indicator_abs_sub_eq_zero_of_eq A hxy)

private lemma dephys_eps_sound_dominates_tv_mass_gap_le_bad_count {State : Type*}
    [Fintype State] [DecidableEq State] (x y : State → Bool) (bad : Finset State)
    (hagree : ∀ ω, ω ∉ bad → x ω = y ω) (A : Finset Bool) :
    |dephys_eps_sound_dominates_tv_eventMass x A -
        dephys_eps_sound_dominates_tv_eventMass y A| ≤ bad.card := by
  classical
  have hsum :
      ∑ ω : State,
          (dephys_eps_sound_dominates_tv_indicator A (x ω) -
            dephys_eps_sound_dominates_tv_indicator A (y ω)) =
        dephys_eps_sound_dominates_tv_eventMass x A -
          dephys_eps_sound_dominates_tv_eventMass y A := by
    simp [dephys_eps_sound_dominates_tv_eventMass, Finset.sum_sub_distrib]
  rw [← hsum]
  calc
    |∑ ω : State,
        (dephys_eps_sound_dominates_tv_indicator A (x ω) -
          dephys_eps_sound_dominates_tv_indicator A (y ω))| ≤
        ∑ ω : State,
          |dephys_eps_sound_dominates_tv_indicator A (x ω) -
            dephys_eps_sound_dominates_tv_indicator A (y ω)| := by
          simpa using
            (Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun ω : State =>
                dephys_eps_sound_dominates_tv_indicator A (x ω) -
                  dephys_eps_sound_dominates_tv_indicator A (y ω)))
    _ ≤ ∑ ω : State, if ω ∈ bad then (1 : ℝ) else 0 := by
      refine Finset.sum_le_sum ?_
      intro ω hω
      exact dephys_eps_sound_dominates_tv_pointwise_bad_bound x y bad hagree A ω
    _ = bad.card := by
      have hcard_nat : (∑ ω : State, if ω ∈ bad then 1 else 0) = bad.card := by
        calc
          (∑ ω : State, if ω ∈ bad then 1 else 0) =
              Finset.sum (Finset.univ.filter fun ω : State => ω ∈ bad) (fun _ => (1 : ℕ)) := by
                simpa using
                  (Finset.sum_filter (s := (Finset.univ : Finset State))
                    (p := fun ω : State => ω ∈ bad) (f := fun _ => (1 : ℕ))).symm
          _ = Finset.sum bad (fun _ => (1 : ℕ)) := by
                simp
          _ = bad.card := by
                rw [Finset.card_eq_sum_ones]
      have hcard_real :
          (((∑ ω : State, if ω ∈ bad then 1 else 0) : ℕ) : ℝ) = bad.card := by
        exact_mod_cast hcard_nat
      simpa using hcard_real

/-- Paper label: `prop:dephys-eps-sound-dominates-tv`. A bad event of probability at most `ε`
on whose complement the two Boolean readouts agree forces every measurable-set discrepancy, and
hence the total variation, to be at most `ε`. -/
theorem paper_dephys_eps_sound_dominates_tv {State : Type*} [Fintype State] [Nonempty State]
    [DecidableEq State] (x y : State → Bool) (bad : Finset State) (ε : ℝ)
    (hagree : ∀ ω, ω ∉ bad → x ω = y ω)
    (hbad : (bad.card : ℝ) / Fintype.card State ≤ ε) :
    dephys_eps_sound_dominates_tv_totalVariation x y ≤ ε := by
  classical
  have hcard_pos : 0 < (Fintype.card State : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty State›
  have hnonempty :
      (Set.range (dephys_eps_sound_dominates_tv_setDiscrepancy x y)).Nonempty := by
    refine ⟨dephys_eps_sound_dominates_tv_setDiscrepancy x y ∅, ⟨∅, rfl⟩⟩
  have hbdd :
      BddAbove (Set.range (dephys_eps_sound_dominates_tv_setDiscrepancy x y)) := by
    refine ⟨ε, ?_⟩
    rintro _ ⟨A, rfl⟩
    have hmass :
        |dephys_eps_sound_dominates_tv_eventMass x A -
            dephys_eps_sound_dominates_tv_eventMass y A| ≤ bad.card := by
      exact dephys_eps_sound_dominates_tv_mass_gap_le_bad_count x y bad hagree A
    have hdiv :
        |dephys_eps_sound_dominates_tv_eventMass x A -
            dephys_eps_sound_dominates_tv_eventMass y A| /
          Fintype.card State ≤
        bad.card / Fintype.card State := by
      exact div_le_div_of_nonneg_right hmass hcard_pos.le
    exact le_trans hdiv hbad
  refine csSup_le hnonempty ?_
  rintro _ ⟨A, rfl⟩
  have hmass :
      |dephys_eps_sound_dominates_tv_eventMass x A -
          dephys_eps_sound_dominates_tv_eventMass y A| ≤ bad.card := by
    exact dephys_eps_sound_dominates_tv_mass_gap_le_bad_count x y bad hagree A
  have hdiv :
      |dephys_eps_sound_dominates_tv_eventMass x A -
          dephys_eps_sound_dominates_tv_eventMass y A| /
        Fintype.card State ≤
      bad.card / Fintype.card State := by
    exact div_le_div_of_nonneg_right hmass hcard_pos.le
  exact le_trans hdiv hbad

end Omega.Zeta

import Mathlib.Tactic
import Mathlib.Topology.Basic

namespace Omega.Zeta

open Filter

universe u

noncomputable section

/-- Dyadic decoding capacity supplied by `b` bits. -/
def xi_full_microstate_exact_inversion_bitrate_threshold_dyadicBudget (b : ℕ) : ℕ :=
  2 ^ b

/-- Finite recovered mass when every fiber can contribute at most the dyadic budget. -/
def xi_full_microstate_exact_inversion_bitrate_threshold_budgetedMass
    {α : Type u} [Fintype α] (fiberMass : α → ℕ) (b : ℕ) : ℕ :=
  ∑ a, min (fiberMass a)
    (xi_full_microstate_exact_inversion_bitrate_threshold_dyadicBudget b)

/-- Total finite fiber mass. -/
def xi_full_microstate_exact_inversion_bitrate_threshold_totalMass
    {α : Type u} [Fintype α] (fiberMass : α → ℕ) : ℕ :=
  ∑ a, fiberMass a

/-- Maximum finite fiber size. -/
def xi_full_microstate_exact_inversion_bitrate_threshold_maxFiberSize
    {α : Type u} [Fintype α] (fiberMass : α → ℕ) : ℕ :=
  Finset.univ.sup fiberMass

/-- Equality of the capped capacity sum with total mass is equivalent to every fiber fitting
inside the dyadic budget. -/
theorem xi_full_microstate_exact_inversion_bitrate_threshold_budgetedMass_eq_total_iff
    {α : Type u} [Fintype α] (fiberMass : α → ℕ) (b : ℕ) :
    xi_full_microstate_exact_inversion_bitrate_threshold_budgetedMass fiberMass b =
        xi_full_microstate_exact_inversion_bitrate_threshold_totalMass fiberMass ↔
      xi_full_microstate_exact_inversion_bitrate_threshold_maxFiberSize fiberMass ≤
        xi_full_microstate_exact_inversion_bitrate_threshold_dyadicBudget b := by
  classical
  unfold xi_full_microstate_exact_inversion_bitrate_threshold_budgetedMass
    xi_full_microstate_exact_inversion_bitrate_threshold_totalMass
    xi_full_microstate_exact_inversion_bitrate_threshold_maxFiberSize
  constructor
  · intro hsum
    rw [Finset.sup_le_iff]
    intro a _ha
    have hle :
        ∀ x ∈ (Finset.univ : Finset α),
          min (fiberMass x)
              (xi_full_microstate_exact_inversion_bitrate_threshold_dyadicBudget b) ≤
            fiberMass x := by
      intro x _hx
      exact min_le_left _ _
    have hpoint :=
      (Finset.sum_eq_sum_iff_of_le hle).mp hsum a (Finset.mem_univ a)
    exact min_eq_left_iff.mp hpoint
  · intro hmax
    apply Finset.sum_congr rfl
    intro a _ha
    have hfiber :
        fiberMass a ≤ xi_full_microstate_exact_inversion_bitrate_threshold_dyadicBudget b := by
      exact (Finset.le_sup (s := (Finset.univ : Finset α)) (f := fiberMass)
        (Finset.mem_univ a)).trans hmax
    exact min_eq_left hfiber

/-- Concrete finite-capacity package for exact microstate inversion. -/
structure xi_full_microstate_exact_inversion_bitrate_threshold_data where
  xi_full_microstate_exact_inversion_bitrate_threshold_fiber : Type u
  xi_full_microstate_exact_inversion_bitrate_threshold_fintype :
    Fintype xi_full_microstate_exact_inversion_bitrate_threshold_fiber
  xi_full_microstate_exact_inversion_bitrate_threshold_fiberMass :
    xi_full_microstate_exact_inversion_bitrate_threshold_fiber → ℕ
  xi_full_microstate_exact_inversion_bitrate_threshold_normalizedThreshold : ℕ → ℝ
  xi_full_microstate_exact_inversion_bitrate_threshold_linearSlope : ℝ
  xi_full_microstate_exact_inversion_bitrate_threshold_linearRate_hyp :
    Tendsto xi_full_microstate_exact_inversion_bitrate_threshold_normalizedThreshold atTop
      (nhds xi_full_microstate_exact_inversion_bitrate_threshold_linearSlope)

namespace xi_full_microstate_exact_inversion_bitrate_threshold_data

/-- Total mass of all finite fibers. -/
def totalFiberMass (D : xi_full_microstate_exact_inversion_bitrate_threshold_data) : ℕ :=
  letI := D.xi_full_microstate_exact_inversion_bitrate_threshold_fintype
  xi_full_microstate_exact_inversion_bitrate_threshold_totalMass
    D.xi_full_microstate_exact_inversion_bitrate_threshold_fiberMass

/-- Finite capacity sum after applying a dyadic budget to each fiber. -/
def budgetedFiberMass (D : xi_full_microstate_exact_inversion_bitrate_threshold_data)
    (b : ℕ) : ℕ :=
  letI := D.xi_full_microstate_exact_inversion_bitrate_threshold_fintype
  xi_full_microstate_exact_inversion_bitrate_threshold_budgetedMass
    D.xi_full_microstate_exact_inversion_bitrate_threshold_fiberMass b

/-- The maximum fiber size controlling exact inversion. -/
def maxFiberSize (D : xi_full_microstate_exact_inversion_bitrate_threshold_data) : ℕ :=
  letI := D.xi_full_microstate_exact_inversion_bitrate_threshold_fintype
  xi_full_microstate_exact_inversion_bitrate_threshold_maxFiberSize
    D.xi_full_microstate_exact_inversion_bitrate_threshold_fiberMass

/-- Exact finite-layer threshold identity. -/
def thresholdIdentity (D : xi_full_microstate_exact_inversion_bitrate_threshold_data) : Prop :=
  ∀ b,
    D.budgetedFiberMass b = D.totalFiberMass ↔
      D.maxFiberSize ≤ xi_full_microstate_exact_inversion_bitrate_threshold_dyadicBudget b

/-- Supplied asymptotic wrapper for the normalized exact-inversion threshold. -/
def linearRate (D : xi_full_microstate_exact_inversion_bitrate_threshold_data) : Prop :=
  Tendsto D.xi_full_microstate_exact_inversion_bitrate_threshold_normalizedThreshold atTop
    (nhds D.xi_full_microstate_exact_inversion_bitrate_threshold_linearSlope)

/-- Above the finite threshold, the capped sum recovers all mass exactly. -/
def supercriticalExact (D : xi_full_microstate_exact_inversion_bitrate_threshold_data) : Prop :=
  ∀ b,
    D.maxFiberSize ≤ xi_full_microstate_exact_inversion_bitrate_threshold_dyadicBudget b →
      D.budgetedFiberMass b = D.totalFiberMass

/-- Below the finite threshold, the capacity sum has a positive missing mass. -/
def subcriticalDefectLowerBound
    (D : xi_full_microstate_exact_inversion_bitrate_threshold_data) : Prop :=
  ∀ b,
    xi_full_microstate_exact_inversion_bitrate_threshold_dyadicBudget b < D.maxFiberSize →
      D.budgetedFiberMass b < D.totalFiberMass

end xi_full_microstate_exact_inversion_bitrate_threshold_data

open xi_full_microstate_exact_inversion_bitrate_threshold_data

/-- Paper label: `thm:xi-full-microstate-exact-inversion-bitrate-threshold`. -/
theorem paper_xi_full_microstate_exact_inversion_bitrate_threshold
    (D : xi_full_microstate_exact_inversion_bitrate_threshold_data) :
    D.thresholdIdentity ∧ D.linearRate ∧ D.supercriticalExact ∧
      D.subcriticalDefectLowerBound := by
  classical
  letI := D.xi_full_microstate_exact_inversion_bitrate_threshold_fintype
  have hThreshold : D.thresholdIdentity := by
    intro b
    dsimp [thresholdIdentity, budgetedFiberMass, totalFiberMass, maxFiberSize]
    exact xi_full_microstate_exact_inversion_bitrate_threshold_budgetedMass_eq_total_iff
      D.xi_full_microstate_exact_inversion_bitrate_threshold_fiberMass b
  have hSuper : D.supercriticalExact := by
    intro b hb
    exact (hThreshold b).2 hb
  have hSub : D.subcriticalDefectLowerBound := by
    intro b hb
    have hcaple : D.budgetedFiberMass b ≤ D.totalFiberMass := by
      dsimp [budgetedFiberMass, totalFiberMass,
        xi_full_microstate_exact_inversion_bitrate_threshold_budgetedMass,
        xi_full_microstate_exact_inversion_bitrate_threshold_totalMass]
      exact Finset.sum_le_sum fun a _ha => min_le_left _ _
    exact lt_of_le_of_ne hcaple fun heq => by
      have hfit := (hThreshold b).1 heq
      exact (not_lt_of_ge hfit) hb
  exact ⟨hThreshold, D.xi_full_microstate_exact_inversion_bitrate_threshold_linearRate_hyp,
    hSuper, hSub⟩

end
end Omega.Zeta

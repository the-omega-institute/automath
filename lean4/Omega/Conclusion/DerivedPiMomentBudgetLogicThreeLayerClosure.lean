import Omega.Conclusion.CollisionGenfuncRadiusHalting
import Omega.Conclusion.DeepfrozenMicroescortOracleThreshold
import Omega.Conclusion.FiniteFiberNaturalExtensionRightShiftInsertion
import Omega.Conclusion.FixedTempSoftOrderProbabilisticFiniteStateDecidable
import Omega.Conclusion.HaltingTimeExternalBudgetExact
import Omega.Conclusion.MinimalStateComplexityHalting
import Omega.Conclusion.PoissonCauchyRenyiSixthNegativeMonotone

namespace Omega.Conclusion

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Concrete moment-side inputs for the three-layer closure wrapper. -/
structure derived_pi_moment_budget_logic_three_layer_closure_moment_data where
  derived_pi_moment_budget_logic_three_layer_closure_moment_mu2 : ℝ
  derived_pi_moment_budget_logic_three_layer_closure_moment_mu3 : ℝ
  derived_pi_moment_budget_logic_three_layer_closure_moment_mu4 : ℝ
  derived_pi_moment_budget_logic_three_layer_closure_moment_mu2_pos :
    0 < derived_pi_moment_budget_logic_three_layer_closure_moment_mu2
  derived_pi_moment_budget_logic_three_layer_closure_moment_pearson :
    derived_pi_moment_budget_logic_three_layer_closure_moment_mu2 *
        derived_pi_moment_budget_logic_three_layer_closure_moment_mu4 ≥
      derived_pi_moment_budget_logic_three_layer_closure_moment_mu3 ^ 2 +
        derived_pi_moment_budget_logic_three_layer_closure_moment_mu2 ^ 3

/-- The imported moment-layer consequence. -/
def derived_pi_moment_budget_logic_three_layer_closure_moment_data_layer
    (D : derived_pi_moment_budget_logic_three_layer_closure_moment_data) : Prop :=
  (∀ {alpha : Real},
      0 < alpha →
        alpha *
            (3 * D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu3 ^ 2 / 32 -
                D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu2 *
                  D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu4 / 8 -
              (alpha - 2) *
                D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu2 ^ 3 / 64) <
          0) ∧
    ∀ {alpha beta : Real},
      0 < alpha →
        alpha < beta →
          beta *
              (3 * D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu3 ^ 2 / 32 -
                  D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu2 *
                    D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu4 / 8 -
                (beta - 2) *
                  D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu2 ^ 3 / 64) <
            alpha *
              (3 * D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu3 ^ 2 / 32 -
                  D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu2 *
                    D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu4 / 8 -
                (alpha - 2) *
                  D.derived_pi_moment_budget_logic_three_layer_closure_moment_mu2 ^ 3 / 64)

/-- Concrete logic-side inputs for the three-layer closure wrapper. -/
structure derived_pi_moment_budget_logic_three_layer_closure_logic_data where
  derived_pi_moment_budget_logic_three_layer_closure_logic_q : ℕ
  derived_pi_moment_budget_logic_three_layer_closure_logic_T : ℕ
  derived_pi_moment_budget_logic_three_layer_closure_logic_hq :
    2 ≤ derived_pi_moment_budget_logic_three_layer_closure_logic_q
  derived_pi_moment_budget_logic_three_layer_closure_logic_halts : Prop
  derived_pi_moment_budget_logic_three_layer_closure_logic_a : ℕ → ℝ
  derived_pi_moment_budget_logic_three_layer_closure_logic_R : ℝ
  derived_pi_moment_budget_logic_three_layer_closure_logic_nonhalt :
    ¬ derived_pi_moment_budget_logic_three_layer_closure_logic_halts →
      ∀ t, derived_pi_moment_budget_logic_three_layer_closure_logic_a t = 1
  derived_pi_moment_budget_logic_three_layer_closure_logic_halt :
    derived_pi_moment_budget_logic_three_layer_closure_logic_halts →
      ∀ t,
        derived_pi_moment_budget_logic_three_layer_closure_logic_T ≤ t →
          derived_pi_moment_budget_logic_three_layer_closure_logic_a t =
            (2 : ℝ) ^
              ((derived_pi_moment_budget_logic_three_layer_closure_logic_q - 1) * (t + 1))
  derived_pi_moment_budget_logic_three_layer_closure_logic_radius_nonhalt :
    ¬ derived_pi_moment_budget_logic_three_layer_closure_logic_halts →
      derived_pi_moment_budget_logic_three_layer_closure_logic_R = 1
  derived_pi_moment_budget_logic_three_layer_closure_logic_radius_halt :
    derived_pi_moment_budget_logic_three_layer_closure_logic_halts →
      derived_pi_moment_budget_logic_three_layer_closure_logic_R =
        1 /
          (2 : ℝ) ^
            (derived_pi_moment_budget_logic_three_layer_closure_logic_q - 1)
  derived_pi_moment_budget_logic_three_layer_closure_logic_soft_data :
    FixedTempSoftOrderProbabilisticFiniteStateDecidableData

/-- The imported logic-layer consequence. -/
def derived_pi_moment_budget_logic_three_layer_closure_logic_data_layer
    (D : derived_pi_moment_budget_logic_three_layer_closure_logic_data) : Prop :=
  let S :=
    D.derived_pi_moment_budget_logic_three_layer_closure_logic_soft_data
  (D.derived_pi_moment_budget_logic_three_layer_closure_logic_R =
      if D.derived_pi_moment_budget_logic_three_layer_closure_logic_halts then
        1 /
          (2 : ℝ) ^
            (D.derived_pi_moment_budget_logic_three_layer_closure_logic_q - 1)
      else 1) ∧
    S.finiteStateClosure ∧ S.distributionEquivalenceDecidable

/-- Concrete budget-side inputs for the three-layer closure wrapper. -/
structure derived_pi_moment_budget_logic_three_layer_closure_budget_data where
  derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data :
    HaltingTimeExternalBudgetExactData
  derived_pi_moment_budget_logic_three_layer_closure_budget_alpha : ℕ
  derived_pi_moment_budget_logic_three_layer_closure_budget_beta : ℕ

/-- The imported budget-layer consequence. -/
def derived_pi_moment_budget_logic_three_layer_closure_budget_data_layer
    (D : derived_pi_moment_budget_logic_three_layer_closure_budget_data) : Prop :=
  ((¬ D.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.halts →
        D.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.externalBudget =
          1) ∧
      (D.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.halts →
        D.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.externalBudget =
          D.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.haltingSteps +
            1)) ∧
    ((∀ m,
          binfoldFrozenEscortReducedSuccess
              D.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha
              D.derived_pi_moment_budget_logic_three_layer_closure_budget_beta m =
            min
                ((2 : ℝ) ^
                  (D.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha * m))
                ((2 : ℝ) ^
                  (D.derived_pi_moment_budget_logic_three_layer_closure_budget_beta * m)) /
              (2 : ℝ) ^
                (D.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha * m)) ∧
      ((D.derived_pi_moment_budget_logic_three_layer_closure_budget_beta <
            D.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha) →
        Filter.Tendsto
          (fun m =>
            binfoldFrozenEscortReducedSuccess
              D.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha
              D.derived_pi_moment_budget_logic_three_layer_closure_budget_beta m)
          Filter.atTop (nhds 0)) ∧
      ((D.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha <
            D.derived_pi_moment_budget_logic_three_layer_closure_budget_beta) →
        Filter.Tendsto
          (fun m =>
            binfoldFrozenEscortReducedSuccess
              D.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha
              D.derived_pi_moment_budget_logic_three_layer_closure_budget_beta m)
          Filter.atTop (nhds 1)))

/-- Concrete bounded-fiber inputs for the three-layer closure wrapper. -/
structure derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_data where
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_X : Type
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T :
    derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_X →
      derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_X
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta :
    derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_X → Nat
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_decode :
    derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_X →
      Nat → derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_X
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_hT :
    ∀ y a,
      derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
          (derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_decode y a) =
        y
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_hbeta :
    ∀ y a,
      derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta
          (derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_decode y a) =
        a
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_hdecode :
    ∀ x,
      derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_decode
          (derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T x)
          (derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta x) =
        x
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_min_state_data :
    ConclusionMinimalStateComplexityHaltingData

/-- The imported bounded-fiber consequence. -/
def derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_data_layer
    (D : derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_data) : Prop :=
  let C :=
    Omega.Folding.branchRegisterCodeToImage
      D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
      D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta
  let G :=
    Omega.Folding.branchRegisterDecodeImage
      D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
      D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta
      D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_decode
      D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_hT
  let N :=
    D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_min_state_data
  (Function.Bijective C ∧
      Function.LeftInverse G C ∧
      Function.RightInverse G C ∧
      ∀ s :
        Omega.Folding.NaturalExtension
          D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T,
        Omega.Folding.branchRegisterShift
            D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
            D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta
            (C s) =
          C
            (Omega.Folding.naturalExtensionShift
              D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T s)) ∧
    ((N.halts → N.minStateCount = N.haltingSteps +
              1) ∧
      (¬ N.halts → N.minStateCount ≤ N.uniformBound) ∧
      N.stateCountEncodesHalting)

/-- Wrapper record whose four concrete fields feed the imported moment, logic, budget, and
bounded-fiber consequence theorems. -/
structure derived_pi_moment_budget_logic_three_layer_closure_data where
  derived_pi_moment_budget_logic_three_layer_closure_moment :
    derived_pi_moment_budget_logic_three_layer_closure_moment_data
  derived_pi_moment_budget_logic_three_layer_closure_logic :
    derived_pi_moment_budget_logic_three_layer_closure_logic_data
  derived_pi_moment_budget_logic_three_layer_closure_budget :
    derived_pi_moment_budget_logic_three_layer_closure_budget_data
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber :
    derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_data

/-- The moment layer in the final wrapper. -/
def derived_pi_moment_budget_logic_three_layer_closure_moment_layer
    (D : derived_pi_moment_budget_logic_three_layer_closure_data) : Prop :=
  derived_pi_moment_budget_logic_three_layer_closure_moment_data_layer
    D.derived_pi_moment_budget_logic_three_layer_closure_moment

/-- The logic layer in the final wrapper. -/
def derived_pi_moment_budget_logic_three_layer_closure_logic_layer
    (D : derived_pi_moment_budget_logic_three_layer_closure_data) : Prop :=
  derived_pi_moment_budget_logic_three_layer_closure_logic_data_layer
    D.derived_pi_moment_budget_logic_three_layer_closure_logic

/-- The budget layer in the final wrapper. -/
def derived_pi_moment_budget_logic_three_layer_closure_budget_layer
    (D : derived_pi_moment_budget_logic_three_layer_closure_data) : Prop :=
  derived_pi_moment_budget_logic_three_layer_closure_budget_data_layer
    D.derived_pi_moment_budget_logic_three_layer_closure_budget

/-- The bounded-fiber layer in the final wrapper. -/
def derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_layer
    (D : derived_pi_moment_budget_logic_three_layer_closure_data) : Prop :=
  derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_data_layer
    D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber

/-- Paper label: `thm:derived-pi-moment-budget-logic-three-layer-closure`. -/
theorem paper_derived_pi_moment_budget_logic_three_layer_closure
    (D : derived_pi_moment_budget_logic_three_layer_closure_data) :
    derived_pi_moment_budget_logic_three_layer_closure_moment_layer D ∧
      derived_pi_moment_budget_logic_three_layer_closure_logic_layer D ∧
      derived_pi_moment_budget_logic_three_layer_closure_budget_layer D ∧
      derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_layer D := by
  let M := D.derived_pi_moment_budget_logic_three_layer_closure_moment
  let L := D.derived_pi_moment_budget_logic_three_layer_closure_logic
  let B := D.derived_pi_moment_budget_logic_three_layer_closure_budget
  let F := D.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber
  have hMoment :
      derived_pi_moment_budget_logic_three_layer_closure_moment_data_layer M := by
    exact paper_conclusion_poisson_cauchy_renyi_sixth_negative_monotone
      (mu2 := M.derived_pi_moment_budget_logic_three_layer_closure_moment_mu2)
      (mu3 := M.derived_pi_moment_budget_logic_three_layer_closure_moment_mu3)
      (mu4 := M.derived_pi_moment_budget_logic_three_layer_closure_moment_mu4)
      M.derived_pi_moment_budget_logic_three_layer_closure_moment_mu2_pos
      M.derived_pi_moment_budget_logic_three_layer_closure_moment_pearson
  have hLogicRadius :
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_R =
        if L.derived_pi_moment_budget_logic_three_layer_closure_logic_halts then
          1 /
            (2 : ℝ) ^
              (L.derived_pi_moment_budget_logic_three_layer_closure_logic_q - 1)
        else 1 := by
    exact paper_conclusion_collision_genfunc_radius_halting
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_q
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_T
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_hq
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_halts
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_a
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_R
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_nonhalt
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_halt
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_radius_nonhalt
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_radius_halt
  have hLogicSoft :
      let S := L.derived_pi_moment_budget_logic_three_layer_closure_logic_soft_data
      S.finiteStateClosure ∧ S.distributionEquivalenceDecidable := by
    exact paper_conclusion_fixed_temp_soft_order_probabilistic_finite_state_decidable
      L.derived_pi_moment_budget_logic_three_layer_closure_logic_soft_data
  have hBudgetExact :
      (¬ B.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.halts →
          B.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.externalBudget =
            1) ∧
        (B.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.halts →
          B.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.externalBudget =
            B.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data.haltingSteps +
              1) := by
    exact paper_conclusion_halting_time_external_budget_exact
      B.derived_pi_moment_budget_logic_three_layer_closure_budget_halting_data
  have hBudgetOracle :
      (∀ m,
          binfoldFrozenEscortReducedSuccess
              B.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha
              B.derived_pi_moment_budget_logic_three_layer_closure_budget_beta m =
            min
                ((2 : ℝ) ^
                  (B.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha * m))
                ((2 : ℝ) ^
                  (B.derived_pi_moment_budget_logic_three_layer_closure_budget_beta * m)) /
              (2 : ℝ) ^
                (B.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha * m)) ∧
        ((B.derived_pi_moment_budget_logic_three_layer_closure_budget_beta <
              B.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha) →
          Filter.Tendsto
            (fun m =>
              binfoldFrozenEscortReducedSuccess
                B.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha
                B.derived_pi_moment_budget_logic_three_layer_closure_budget_beta m)
            Filter.atTop (nhds 0)) ∧
        ((B.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha <
              B.derived_pi_moment_budget_logic_three_layer_closure_budget_beta) →
          Filter.Tendsto
            (fun m =>
              binfoldFrozenEscortReducedSuccess
                B.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha
                B.derived_pi_moment_budget_logic_three_layer_closure_budget_beta m)
            Filter.atTop (nhds 1)) := by
    exact paper_conclusion_deepfrozen_microescort_oracle_threshold
      B.derived_pi_moment_budget_logic_three_layer_closure_budget_alpha
      B.derived_pi_moment_budget_logic_three_layer_closure_budget_beta
  have hFiber :
      (Function.Bijective
          (Omega.Folding.branchRegisterCodeToImage
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta) ∧
        Function.LeftInverse
          (Omega.Folding.branchRegisterDecodeImage
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_decode
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_hT)
          (Omega.Folding.branchRegisterCodeToImage
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta) ∧
        Function.RightInverse
          (Omega.Folding.branchRegisterDecodeImage
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_decode
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_hT)
          (Omega.Folding.branchRegisterCodeToImage
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta) ∧
        ∀ s :
          Omega.Folding.NaturalExtension
            F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T,
          Omega.Folding.branchRegisterShift
              F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
              F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta
              (Omega.Folding.branchRegisterCodeToImage
                F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
                F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta s) =
            Omega.Folding.branchRegisterCodeToImage
              F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
              F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta
              (Omega.Folding.naturalExtensionShift
                F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T s)) := by
    exact paper_conclusion_finite_fiber_natural_extension_right_shift_insertion
      F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_T
      F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_beta
      F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_decode
      F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_hT
      F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_hbeta
      F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_hdecode
  have hMinState :
      let N := F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_min_state_data
      (N.halts → N.minStateCount = N.haltingSteps + 1) ∧
        (¬ N.halts → N.minStateCount ≤ N.uniformBound) ∧
        N.stateCountEncodesHalting := by
    exact paper_conclusion_minimal_state_complexity_halting
      F.derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_min_state_data
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [derived_pi_moment_budget_logic_three_layer_closure_moment_layer, M] using hMoment
  · simpa [derived_pi_moment_budget_logic_three_layer_closure_logic_layer,
      derived_pi_moment_budget_logic_three_layer_closure_logic_data_layer, L] using
      And.intro hLogicRadius hLogicSoft
  · simpa [derived_pi_moment_budget_logic_three_layer_closure_budget_layer,
      derived_pi_moment_budget_logic_three_layer_closure_budget_data_layer, B] using
      And.intro hBudgetExact hBudgetOracle
  · simpa [derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_layer,
      derived_pi_moment_budget_logic_three_layer_closure_bounded_fiber_data_layer, F] using
      And.intro hFiber hMinState

end

end Omega.Conclusion

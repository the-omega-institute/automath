import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.TqftGenusHausdorffMomentSequence
import Omega.DerivedConsequences.DerivedProjectivePath2RMomentsRecoverSpectrum
import Omega.OperatorAlgebra.FoldChannelChoiRankEqualsS2General
import Omega.OperatorAlgebra.FoldWatataniIndexMoments
import Omega.POM.OracleCapacityStieltjesInversionMellin

namespace Omega.DerivedConsequences

open scoped BigOperators

/-- Histogram count of the multiplicity layer `k`. -/
def derived_finite_moments_complete_operator_topology_capacity_histogram {X : Type*} [Fintype X]
    (d : X → ℕ) (k : ℕ) : ℕ :=
  Fintype.card {x : X // d x = k}

/-- `q`-fold Choi-rank style power sum of a finite multiplicity function. -/
def derived_finite_moments_complete_operator_topology_capacity_qfold_choi_rank {X : Type*}
    [Fintype X] (d : X → ℕ) (q : ℕ) : ℕ :=
  ∑ x, d x ^ q

section

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
private theorem derived_finite_moments_complete_operator_topology_capacity_value_le_total
    (d : X → ℕ) (x : X) : d x ≤ ∑ y, d y := by
  simpa using
    (Finset.single_le_sum (f := fun y : X => d y) (fun y _ => Nat.zero_le (d y))
      (Finset.mem_univ x))

private theorem derived_finite_moments_complete_operator_topology_capacity_sum_nat
    (d : X → ℕ) (w : ℕ → ℕ) :
    (∑ x, w (d x)) =
      Finset.sum (Finset.range ((Finset.sum Finset.univ d) + 1)) fun k =>
        derived_finite_moments_complete_operator_topology_capacity_histogram d k * w k := by
  let M : ℕ := Finset.sum Finset.univ d
  calc
    ∑ x, w (d x)
        =
          ∑ x,
            Finset.sum (Finset.range (M + 1)) fun k => if d x = k then w k else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              have hxM : d x < M + 1 := Nat.lt_succ_of_le
                (derived_finite_moments_complete_operator_topology_capacity_value_le_total d x)
              rw [Finset.sum_eq_single_of_mem (d x) (Finset.mem_range.mpr hxM)]
              · simp
              · intro k hk hneq
                by_cases hdk : d x = k
                · exfalso
                  exact hneq hdk.symm
                · simp [hdk]
    _ =
          Finset.sum (Finset.range (M + 1)) fun k =>
            ∑ x, if d x = k then w k else 0 := by
              rw [Finset.sum_comm]
    _ =
          Finset.sum (Finset.range (M + 1)) fun k =>
            Finset.sum ((Finset.univ : Finset X).filter (fun x => d x = k)) fun _ => w k := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.sum_filter]
    _ =
          Finset.sum (Finset.range (M + 1)) fun k =>
            derived_finite_moments_complete_operator_topology_capacity_histogram d k * w k := by
              apply Finset.sum_congr rfl
              intro k hk
              unfold derived_finite_moments_complete_operator_topology_capacity_histogram
              rw [Fintype.card_of_subtype (Finset.univ.filter fun x => d x = k) (by
                intro x
                simp)]
              simp

private theorem derived_finite_moments_complete_operator_topology_capacity_sum_rat
    (d : X → ℕ) (w : ℕ → ℚ) :
    (∑ x, w (d x)) =
      Finset.sum (Finset.range ((Finset.sum Finset.univ d) + 1)) fun k =>
        (derived_finite_moments_complete_operator_topology_capacity_histogram d k : ℚ) * w k := by
  let M : ℕ := Finset.sum Finset.univ d
  calc
    ∑ x, w (d x)
        =
          ∑ x,
            Finset.sum (Finset.range (M + 1)) fun k => if d x = k then w k else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              have hxM : d x < M + 1 := Nat.lt_succ_of_le
                (derived_finite_moments_complete_operator_topology_capacity_value_le_total d x)
              rw [Finset.sum_eq_single_of_mem (d x) (Finset.mem_range.mpr hxM)]
              · simp
              · intro k hk hneq
                by_cases hdk : d x = k
                · exfalso
                  exact hneq hdk.symm
                · simp [hdk]
    _ =
          Finset.sum (Finset.range (M + 1)) fun k =>
            ∑ x, if d x = k then w k else 0 := by
              rw [Finset.sum_comm]
    _ =
          Finset.sum (Finset.range (M + 1)) fun k =>
            Finset.sum ((Finset.univ : Finset X).filter (fun x => d x = k)) fun _ => w k := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.sum_filter]
    _ =
          Finset.sum (Finset.range (M + 1)) fun k =>
            (derived_finite_moments_complete_operator_topology_capacity_histogram d k : ℚ) * w k := by
              apply Finset.sum_congr rfl
              intro k hk
              unfold derived_finite_moments_complete_operator_topology_capacity_histogram
              rw [Fintype.card_of_subtype (Finset.univ.filter fun x => d x = k) (by
                intro x
                simp)]
              simp

end

/-- Chapter-local completeness package: the already formalized first-`2r` moment theorem recovers
the finite spectrum, and every operator-topology/capacity observable appearing here is an explicit
histogram sum. -/
def DerivedFiniteMomentsCompleteOperatorTopologyCapacityStatement : Prop :=
  (∀ D : Omega.POM.ProjectivePathAtomicPronyData,
    derived_projective_path_2r_moments_recover_spectrum_statement D) ∧
    (∀ {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]
        (fold : Ω → X) (m q B : ℕ) (_hcard : Fintype.card Ω = 2 ^ m),
      let d : X → ℕ := Omega.POM.oracleFiberMultiplicity fold
      let M : ℕ := Finset.sum Finset.univ d
      (Omega.OperatorAlgebra.foldWatataniTracedIndexMoment fold q =
        (Finset.sum (Finset.range (M + 1)) fun k =>
          (derived_finite_moments_complete_operator_topology_capacity_histogram d k : ℚ) *
            (k : ℚ) ^ (q + 1)) /
          2 ^ m) ∧
      (Omega.POM.bbitOracleCapacity fold B =
        Finset.sum (Finset.range (M + 1)) fun k =>
          derived_finite_moments_complete_operator_topology_capacity_histogram d k *
            Nat.min k (2 ^ B)) ∧
      (derived_finite_moments_complete_operator_topology_capacity_qfold_choi_rank d q =
        Finset.sum (Finset.range (M + 1)) fun k =>
          derived_finite_moments_complete_operator_topology_capacity_histogram d k * k ^ q)) ∧
    (∀ D : Omega.OperatorAlgebra.FoldChannelChoiRankData,
      D.choiRank = Finset.univ.sum fun y : Fin D.m => (D.fiberCard y) ^ 2) ∧
    (∀ D : Omega.Conclusion.conclusion_tqft_genus_hausdorff_moment_sequence_data,
      D.conclusion_tqft_genus_hausdorff_moment_sequence_moment_representation)

/-- Paper label: `thm:derived-finite-moments-complete-operator-topology-capacity`. -/
theorem paper_derived_finite_moments_complete_operator_topology_capacity :
    DerivedFiniteMomentsCompleteOperatorTopologyCapacityStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D
    exact paper_derived_projective_path_2r_moments_recover_spectrum D
  · intro Ω X _ _ _ _ fold m q B hcard
    dsimp
    constructor
    · have hMoment :=
        (Omega.OperatorAlgebra.paper_op_algebra_fold_watatani_index_moments fold m q hcard).2.2
      calc
        Omega.OperatorAlgebra.foldWatataniTracedIndexMoment fold q
            = (∑ x : X, (Omega.POM.oracleFiberMultiplicity fold x : ℚ) ^ (q + 1)) / 2 ^ m := by
                simpa [Omega.POM.oracleFiberMultiplicity] using hMoment
        _ =
            (Finset.sum
              (Finset.range ((Finset.sum Finset.univ (Omega.POM.oracleFiberMultiplicity fold)) + 1))
              fun k =>
              (derived_finite_moments_complete_operator_topology_capacity_histogram
                  (Omega.POM.oracleFiberMultiplicity fold) k : ℚ) *
                (k : ℚ) ^ (q + 1)) /
              2 ^ m := by
                congr 1
                exact derived_finite_moments_complete_operator_topology_capacity_sum_rat
                  (d := Omega.POM.oracleFiberMultiplicity fold)
                  (w := fun k => (k : ℚ) ^ (q + 1))
    constructor
    · have hPackage := Omega.POM.paper_pom_oracle_capacity_stieltjes_inversion_mellin fold
      have hCurve : Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve
            (Omega.POM.oracleFiberMultiplicity fold) (2 ^ B) =
          Omega.POM.bbitOracleCapacity fold B := hPackage.1 B
      calc
        Omega.POM.bbitOracleCapacity fold B
            = Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve
                (Omega.POM.oracleFiberMultiplicity fold) (2 ^ B) := by
                  exact hCurve.symm
        _ = Finset.sum
              (Finset.range ((Finset.sum Finset.univ (Omega.POM.oracleFiberMultiplicity fold)) + 1))
              (fun k =>
              derived_finite_moments_complete_operator_topology_capacity_histogram
                  (Omega.POM.oracleFiberMultiplicity fold) k *
                Nat.min k (2 ^ B)) := by
              unfold Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve
              exact derived_finite_moments_complete_operator_topology_capacity_sum_nat
                (d := Omega.POM.oracleFiberMultiplicity fold) (w := fun k => Nat.min k (2 ^ B))
    · unfold derived_finite_moments_complete_operator_topology_capacity_qfold_choi_rank
      exact derived_finite_moments_complete_operator_topology_capacity_sum_nat
        (d := Omega.POM.oracleFiberMultiplicity fold) (w := fun k => k ^ q)
  · intro D
    exact (Omega.OperatorAlgebra.paper_fold_channel_choi_rank_equals_s2_general D).1
  · intro D
    exact (Omega.Conclusion.paper_conclusion_tqft_genus_hausdorff_moment_sequence D).1

end Omega.DerivedConsequences

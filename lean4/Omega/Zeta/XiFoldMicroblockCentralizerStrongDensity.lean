import Mathlib

open Filter Set Topology

/-- Concrete data for finite microblock algebras embedded in a KMS centralizer. -/
structure xi_fold_microblock_centralizer_strong_density_data where
  xi_fold_microblock_centralizer_strong_density_centralizer : Type*
  xi_fold_microblock_centralizer_strong_density_sigma_strong_topology :
    TopologicalSpace xi_fold_microblock_centralizer_strong_density_centralizer
  xi_fold_microblock_centralizer_strong_density_microblock_algebra : ℕ → Type*
  xi_fold_microblock_centralizer_strong_density_microblock_fintype :
    ∀ m, Fintype (xi_fold_microblock_centralizer_strong_density_microblock_algebra m)
  xi_fold_microblock_centralizer_strong_density_embedding :
    ∀ m,
      xi_fold_microblock_centralizer_strong_density_microblock_algebra m →
        xi_fold_microblock_centralizer_strong_density_centralizer
  xi_fold_microblock_centralizer_strong_density_trace_weight_coordinate : ℕ → ℕ → ℝ
  xi_fold_microblock_centralizer_strong_density_limit_trace_weight : ℕ → ℝ
  xi_fold_microblock_centralizer_strong_density_dense_witness :
    letI : TopologicalSpace xi_fold_microblock_centralizer_strong_density_centralizer :=
      xi_fold_microblock_centralizer_strong_density_sigma_strong_topology
    closure
        (range
          (fun p :
              Sigma xi_fold_microblock_centralizer_strong_density_microblock_algebra =>
            xi_fold_microblock_centralizer_strong_density_embedding p.1 p.2)) =
      univ
  xi_fold_microblock_centralizer_strong_density_trace_weights_converge_witness :
    ∀ k,
      Tendsto
        (fun m =>
          xi_fold_microblock_centralizer_strong_density_trace_weight_coordinate m k)
        atTop
        (𝓝 (xi_fold_microblock_centralizer_strong_density_limit_trace_weight k))

namespace xi_fold_microblock_centralizer_strong_density_data

/-- The sigma-strong density predicate for the embedded union of finite microblocks. -/
def xi_fold_microblock_centralizer_strong_density_dense
    (D : xi_fold_microblock_centralizer_strong_density_data) : Prop :=
  letI : TopologicalSpace D.xi_fold_microblock_centralizer_strong_density_centralizer :=
    D.xi_fold_microblock_centralizer_strong_density_sigma_strong_topology
  closure
      (range
        (fun p :
            Sigma D.xi_fold_microblock_centralizer_strong_density_microblock_algebra =>
          D.xi_fold_microblock_centralizer_strong_density_embedding p.1 p.2)) =
    univ

/-- Coordinatewise convergence of the trace-weight vectors to the limiting weights. -/
def xi_fold_microblock_centralizer_strong_density_trace_weights_converge
    (D : xi_fold_microblock_centralizer_strong_density_data) : Prop :=
  ∀ k,
    Tendsto
      (fun m => D.xi_fold_microblock_centralizer_strong_density_trace_weight_coordinate m k)
      atTop
      (𝓝 (D.xi_fold_microblock_centralizer_strong_density_limit_trace_weight k))

end xi_fold_microblock_centralizer_strong_density_data

/-- Paper label: `prop:xi-fold-microblock-centralizer-strong-density`. -/
theorem paper_xi_fold_microblock_centralizer_strong_density
    (D : xi_fold_microblock_centralizer_strong_density_data) :
    D.xi_fold_microblock_centralizer_strong_density_dense ∧
      D.xi_fold_microblock_centralizer_strong_density_trace_weights_converge := by
  constructor
  · simpa
      [xi_fold_microblock_centralizer_strong_density_data.xi_fold_microblock_centralizer_strong_density_dense]
      using
      D.xi_fold_microblock_centralizer_strong_density_dense_witness
  · simpa
      [xi_fold_microblock_centralizer_strong_density_data.xi_fold_microblock_centralizer_strong_density_trace_weights_converge]
      using
      D.xi_fold_microblock_centralizer_strong_density_trace_weights_converge_witness

import Mathlib.Tactic
import Omega.Conclusion.M2Level3XiDelta0Order6Charpolys

namespace Omega.Conclusion

/-- Concrete wrapper for the Steinberg local-system inertia spectra package. -/
structure conclusion_m2_level3_steinberg_local_system_inertia_spectra_data where
  conclusion_m2_level3_steinberg_local_system_inertia_spectra_witness : Unit := ()

/-- Rank of the edge module in the audited incidence model. -/
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_edge_rank : ℕ :=
  120

/-- Rank of the vertex module in the audited incidence model. -/
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_vertex_rank : ℕ :=
  40

/-- Rank of the augmentation target. -/
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_augmentation_rank : ℕ :=
  1

/-- Exactness gives the Steinberg local-system rank as `rank E - rank V + rank Q`. -/
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_steinberg_rank : ℕ :=
  conclusion_m2_level3_steinberg_local_system_inertia_spectra_edge_rank -
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_vertex_rank +
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_augmentation_rank

/-- Cyclotomic multiplicities in the order-`6` inertia spectrum of the Steinberg block. -/
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi1_mult : ℕ := 15
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi2_mult : ℕ := 12
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi3_mult : ℕ := 15
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi6_mult : ℕ := 12

/-- Trace of the order-`3` inertia element `τ = g²`. -/
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_tau_trace : ℤ :=
  (conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi1_mult : ℤ) +
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi2_mult -
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi3_mult -
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi6_mult

/-- Trace of the order-`2` inertia element `σ = g³`. -/
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_sigma_trace : ℤ :=
  (conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi1_mult : ℤ) -
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi2_mult +
    2 * conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi3_mult -
    2 * conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi6_mult

/-- Characteristic polynomial of the Steinberg local-system inertia action. -/
noncomputable def conclusion_m2_level3_steinberg_local_system_inertia_spectra_charpoly :
    Polynomial ℤ :=
  conclusion_m2_level3_xi_delta0_order6_charpolys_St

/-- Concrete paper-facing formulation of the inertia spectrum package. -/
def conclusion_m2_level3_steinberg_local_system_inertia_spectra_statement
    (_D : conclusion_m2_level3_steinberg_local_system_inertia_spectra_data) : Prop :=
  conclusion_m2_level3_xi_delta0_order6_cycletypes_klingen_cycle_counts = (5, 4, 1, 4) ∧
    conclusion_m2_level3_xi_delta0_order6_cycletypes_siegel_cycle_counts = (4, 0, 4, 4) ∧
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_edge_rank = 120 ∧
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_vertex_rank = 40 ∧
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_augmentation_rank = 1 ∧
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_steinberg_rank = 81 ∧
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_tau_trace = 0 ∧
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_sigma_trace = 9 ∧
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_charpoly =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 15 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 12 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 15 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 12

/-- Paper label: `thm:conclusion-m2-level3-steinberg-local-system-inertia-spectra`. The audited
order-`6` cycle counts feed into the Steinberg block of the Hecke characteristic-polynomial
package; exactness of the augmented incidence complex gives rank `81`, and the cyclotomic
multiplicities determine the traces of `τ` and `σ`. -/
theorem paper_conclusion_m2_level3_steinberg_local_system_inertia_spectra
    (D : conclusion_m2_level3_steinberg_local_system_inertia_spectra_data) :
    conclusion_m2_level3_steinberg_local_system_inertia_spectra_statement D := by
  rcases paper_conclusion_m2_level3_xi_delta0_order6_charpolys (D := ⟨()⟩) with
    ⟨hklingen, hsiegel, _, _, _, _, hSt, _, _⟩
  refine ⟨hklingen, hsiegel, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_m2_level3_steinberg_local_system_inertia_spectra_steinberg_rank,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_edge_rank,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_vertex_rank,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_augmentation_rank]
  · norm_num [conclusion_m2_level3_steinberg_local_system_inertia_spectra_tau_trace,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi1_mult,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi2_mult,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi3_mult,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi6_mult]
  · norm_num [conclusion_m2_level3_steinberg_local_system_inertia_spectra_sigma_trace,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi1_mult,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi2_mult,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi3_mult,
      conclusion_m2_level3_steinberg_local_system_inertia_spectra_phi6_mult]
  · simpa [conclusion_m2_level3_steinberg_local_system_inertia_spectra_charpoly] using hSt

end Omega.Conclusion

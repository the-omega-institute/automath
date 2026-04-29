import Omega.Conclusion.Window6FiberGaugeLaplacianProjectors
import Omega.GU.Window6EdgeFluxCommutantRigidity
import Omega.GU.Window6EdgeFluxNoInvariantBilinearForm
import Omega.GU.Window6EdgeFluxNoInvariantBinaryProduct
import Omega.GU.Window6LieEnvelopeSL21

namespace Omega.Conclusion

/-- Paper-facing Window 6 ambient package: projector synthesis, commutant rigidity, absence of
invariant bilinear forms and binary products, full matrix saturation, and the audited `sl(21)`
Lie-envelope certificate. -/
def conclusion_window6_observable_sectors_vs_cartan_saturated_ambient_statement : Prop :=
  conclusion_window6_fiber_gauge_laplacian_projectors_statement ∧
    (∀ L : Fin 6 → Matrix (Fin 21) (Fin 21) ℝ,
      Omega.GU.Window6LieEnvelopeIsSl21 L →
        Omega.GU.Window6EdgeFluxFullMatrixSaturation L ∧
          (∀ T : Matrix (Fin 21) (Fin 21) ℝ,
            (∀ i : Fin 6, T * L i = L i * T) →
              ∃ c : ℝ, T = c • (1 : Matrix (Fin 21) (Fin 21) ℝ)) ∧
          (∀ S : Matrix (Fin 21) (Fin 21) ℝ,
            (∀ X : Matrix (Fin 21) (Fin 21) ℝ, X ∈ Omega.GU.window6EdgeFluxClosure L →
              X.transpose * S + S * X = 0) →
              S = 0)) ∧
    (∀ D : Omega.GU.Window6EdgeFluxDynamicsData, D.noInvariantBinaryProduct) ∧
    Omega.GU.window6FullEnvelopeIsSpecialLinear

/-- Paper label: `thm:conclusion-window6-observable-sectors-vs-cartan-saturated-ambient`. -/
theorem paper_conclusion_window6_observable_sectors_vs_cartan_saturated_ambient :
    conclusion_window6_observable_sectors_vs_cartan_saturated_ambient_statement := by
  refine ⟨paper_conclusion_window6_fiber_gauge_laplacian_projectors, ?_, ?_, ?_⟩
  · intro L hLie
    exact ⟨Omega.GU.paper_window6_edge_flux_full_matrix_saturation L hLie,
      Omega.GU.paper_window6_edge_flux_commutant_rigidity L hLie,
      Omega.GU.paper_window6_edge_flux_no_invariant_bilinear_form L hLie⟩
  · intro D
    exact Omega.GU.paper_window6_edge_flux_no_invariant_binary_product D
  · exact Omega.GU.paper_window6_push_envelope_certificate_upgrade.2.1

end Omega.Conclusion

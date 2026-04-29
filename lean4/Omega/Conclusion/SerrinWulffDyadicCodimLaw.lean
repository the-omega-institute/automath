import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Conclusion.BoundarySubcriticalPerturbationSecondOrderRigidity
import Omega.Conclusion.SerrinRealizableMeanConeCollapse
import Omega.SPG.DyadicOuterApproxStokesGainMinkowskiReadout

namespace Omega.Conclusion

/-- The dyadic flux-zeta residue contributed by the scaled Hausdorff content. -/
noncomputable def conclusion_serrin_wulff_dyadic_codim_law_residue (scaledHausdorff : ℝ) : ℝ :=
  scaledHausdorff / Real.log 2

/-- Paper label: `thm:conclusion-serrin-wulff-dyadic-codim-law`. Modeling the realizable Serrin
class as the positive ray through a fixed Wulff observable, the existing SPG Stokes/Minkowski
readout gives the dyadic codimension relation and flux envelope, the smooth-boundary perturbation
theorem transports the dyadic counting asymptotic, and substituting the Hausdorff scaling law
identifies the critical residue. -/
theorem paper_conclusion_serrin_wulff_dyadic_codim_law
    {n d : ℕ} (vWK : Fin d → ℝ)
    (ambientDim minkowskiDim envelopeConst dωNorm probeReadout : ℝ)
    (flux volume probeFlux : ℕ → ℝ)
    (countDim : ℕ) (M scaledHausdorff ρ hausdorffMeasure : ℝ)
    (volA volV boundaryError : ℕ → ℝ)
    (hNorm : 0 ≤ dωNorm)
    (hStokes : ∀ m, |flux m| ≤ dωNorm * volume m)
    (hEnvelope : ∀ m,
      volume m ≤ envelopeConst * Omega.SPG.dyadicOuterApproxDecay ambientDim minkowskiDim m)
    (hProbe : ∀ m, probeFlux m = volume m)
    (hReadout : minkowskiDim = ambientDim + probeReadout)
    (hA :
      conclusion_boundary_subcritical_perturbation_second_order_rigidity_has_asymptotic
        (conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volA) countDim M)
    (hGap :
      ∀ m,
        |conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volV m -
            conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volA m| ≤
          conclusion_boundary_subcritical_perturbation_second_order_rigidity_scale countDim m *
            |boundaryError m|)
    (hBoundary : Filter.Tendsto boundaryError Filter.atTop (nhds 0))
    (hMpos : 0 < M)
    (hScale :
      scaledHausdorff = Real.rpow ρ (ambientDim - minkowskiDim) * hausdorffMeasure) :
    Set.range
        (conclusion_serrin_realizable_mean_cone_collapse_observable (n := n) vWK) =
      conclusion_serrin_realizable_mean_cone_collapse_positive_ray vWK ∧
      (∀ m, |flux m| ≤
        (dωNorm * envelopeConst) * Omega.SPG.dyadicOuterApproxDecay ambientDim minkowskiDim m) ∧
      minkowskiDim = ambientDim + probeReadout ∧
      conclusion_boundary_subcritical_perturbation_second_order_rigidity_has_asymptotic
        (conclusion_boundary_subcritical_perturbation_second_order_rigidity_count n volV) countDim M ∧
      conclusion_serrin_wulff_dyadic_codim_law_residue scaledHausdorff =
        Real.rpow ρ (ambientDim - minkowskiDim) * hausdorffMeasure / Real.log 2 := by
  have hrange :
      Set.range (conclusion_serrin_realizable_mean_cone_collapse_observable (n := n) vWK) =
        conclusion_serrin_realizable_mean_cone_collapse_positive_ray vWK := by
    ext w
    constructor
    · rintro ⟨Ω, rfl⟩
      exact ⟨Ω.2.1, Ω.2.2, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨(0, ⟨σ, hσ⟩), by
        simp [conclusion_serrin_realizable_mean_cone_collapse_observable]⟩
  have hspg :=
    Omega.SPG.paper_spg_dyadic_outer_approx_stokes_gain_minkowski_readout ambientDim minkowskiDim
      envelopeConst dωNorm probeReadout flux volume probeFlux hNorm hStokes hEnvelope hProbe
      hReadout
  have hrig :=
    paper_conclusion_boundary_subcritical_perturbation_second_order_rigidity n countDim M volA
      volV boundaryError hA hGap hBoundary hMpos
  refine ⟨hrange, hspg.1, hspg.2.2, hrig.1, ?_⟩
  rw [conclusion_serrin_wulff_dyadic_codim_law_residue, hScale]

end Omega.Conclusion

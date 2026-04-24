import Omega.Conclusion.CompleteStrictificationDualCriterion

namespace Omega.Conclusion

theorem paper_conclusion_zero_sizebiased_residual_layerwise_rigidity
    {n : ℕ} (residual : Fin n → ℕ) :
    Omega.Conclusion.zeroSizebiasedResidual residual ↔
      Omega.Conclusion.localSizeBiasRigidity residual := by
  exact zero_sum_nat_iff_forall_zero residual

end Omega.Conclusion

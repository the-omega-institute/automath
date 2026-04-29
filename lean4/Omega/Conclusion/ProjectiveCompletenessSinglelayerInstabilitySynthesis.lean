import Mathlib
import Omega.CircleDimension.CertificateInverseLimitAddressing
import Omega.SPG.DyadicTopInversionBound

namespace Omega.Conclusion

structure conclusion_projective_completeness_singlelayer_instability_synthesis_data where
  Cert : Type
  pointsTo : Cert → ℝ → Prop
  equiv : Cert → Cert → Prop
  left : Cert → ℝ
  right : Cert → ℝ
  chain : ℕ → Cert
  hnested :
    ∀ n,
      Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) ⊆
        Set.Icc (left (chain n)) (right (chain n))
  hdiam :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, right (chain n) - left (chain n) < ε
  hclosed : ∀ n, left (chain n) ≤ right (chain n)
  hmerge : ∀ C C' θ, pointsTo C θ → pointsTo C' θ → equiv C C'
  scale : ℕ
  dimension : ℕ
  dimension_pos : 1 ≤ dimension

def conclusion_projective_completeness_singlelayer_instability_synthesis_statement
    (D : conclusion_projective_completeness_singlelayer_instability_synthesis_data) : Prop :=
  (∃! θ : ℝ,
      (∀ n, θ ∈ Set.Icc (D.left (D.chain n)) (D.right (D.chain n))) ∧
        ∀ C C', D.pointsTo C θ → D.pointsTo C' θ → D.equiv C C') ∧
    ((Omega.SPG.boundaryCellCount D.scale D.dimension : ℝ) /
        (Omega.SPG.topCellCount D.scale D.dimension : ℝ) =
      (2 * D.dimension : ℝ) / 2 ^ D.scale)

theorem paper_conclusion_projective_completeness_singlelayer_instability_synthesis
    (D : conclusion_projective_completeness_singlelayer_instability_synthesis_data) :
    conclusion_projective_completeness_singlelayer_instability_synthesis_statement D := by
  refine ⟨?_, ?_⟩
  · exact Omega.CircleDimension.paper_cdim_certificate_inverse_limit_addressing D.pointsTo D.equiv
      D.left D.right D.chain D.hnested D.hdiam D.hclosed D.hmerge
  · exact
      (Omega.SPG.paper_spg_dyadic_top_inversion_ill_conditioning).2.2.1
        D.scale D.dimension D.dimension_pos

end Omega.Conclusion

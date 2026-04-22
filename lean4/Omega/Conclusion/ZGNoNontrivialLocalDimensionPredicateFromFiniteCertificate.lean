import Omega.Conclusion.ZGFinitePrefixShadowLocalDimensionBlindness

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-zg-no-nontrivial-local-dimension-predicate-from-finite-certificate`. -/
theorem paper_conclusion_zg_no_nontrivial_local_dimension_predicate_from_finite_certificate
    (D : ZGFinitePrefixShadowLocalDimensionBlindnessData) (P : D.LocalDimensionValue → Prop)
    [DecidablePred P] (hAlpha0 : P D.alpha₀) (hAlpha1 : ¬ P D.alpha₁) :
    ¬ ∃ psi : D.Certificate → D.Shadow → Bool,
      ∀ z, D.localDimensionDefined z →
        psi (D.certificate z) (D.shadow z) = decide (P (D.localDimension z)) := by
  intro hpsi
  rcases hpsi with ⟨psi, hpsi⟩
  let z0 := D.realize D.baseCertificate D.baseShadow D.alpha₀
  let z1 := D.realize D.baseCertificate D.baseShadow D.alpha₁
  have hz0 : psi (D.certificate z0) (D.shadow z0) = decide (P (D.localDimension z0)) := by
    exact hpsi z0 (by simpa [z0] using D.realize_defined D.baseCertificate D.baseShadow D.alpha₀)
  have hz1 : psi (D.certificate z1) (D.shadow z1) = decide (P (D.localDimension z1)) := by
    exact hpsi z1 (by simpa [z1] using D.realize_defined D.baseCertificate D.baseShadow D.alpha₁)
  have hsame :
      psi (D.certificate z0) (D.shadow z0) = psi (D.certificate z1) (D.shadow z1) := by
    simp [z0, z1, D.realize_certificate, D.realize_shadow]
  have hdec0 : decide (P (D.localDimension z0)) = true := by
    simp [z0, D.realize_localDimension, hAlpha0]
  have hdec1 : decide (P (D.localDimension z1)) = false := by
    simp [z1, D.realize_localDimension, hAlpha1]
  have : true = false := by
    calc
      true = decide (P (D.localDimension z0)) := hdec0.symm
      _ = psi (D.certificate z0) (D.shadow z0) := hz0.symm
      _ = psi (D.certificate z1) (D.shadow z1) := hsame
      _ = decide (P (D.localDimension z1)) := hz1
      _ = false := hdec1
  cases this

end Omega.Conclusion

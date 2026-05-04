import Omega.POM.InfonceFiberSpectrumTomographyMinimality

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-infonce-tomography-dimension-exact`. -/
theorem paper_conclusion_infonce_tomography_dimension_exact
    (N : ℕ)
    (beta : ℕ → ℕ → ℝ)
    (spectrumPowerSum lossPowerSum : ℕ → ℝ)
    (hdiag : ∀ K, 2 ≤ K → K ≤ N → beta K K != 0)
    (hloss :
      ∀ K, 2 ≤ K → K ≤ N →
        Finset.sum (Finset.Icc 2 K) (fun q => beta K q * spectrumPowerSum q) =
          Finset.sum (Finset.Icc 2 K) (fun q => beta K q * lossPowerSum q))
    (newtonSize : ℕ)
    (newtonKernel : Fin newtonSize → ℕ → ℝ)
    (pronySize : ℕ)
    (pronyKernel : Fin pronySize → ℕ → ℝ) :
    (let D : Omega.Folding.FoldInfoNCELossTowerNewtonPronyData :=
      { N := N
        beta := beta
        spectrumPowerSum := spectrumPowerSum
        lossPowerSum := lossPowerSum
        hdiag := hdiag
        hloss := hloss
        newtonSize := newtonSize
        newtonKernel := newtonKernel
        pronySize := pronySize
        pronyKernel := pronyKernel }
      ; D.newtonPronyCompleteness) ∧
      ∀ r : ℕ, r < N - 1 →
        ∀ f : (Fin (N - 1) → ℝ) →L[ℝ] (Fin r → ℝ), ¬ Function.Injective f := by
  simpa using
    Omega.POM.paper_pom_infonce_fiber_spectrum_tomography_minimality
      N beta spectrumPowerSum lossPowerSum hdiag hloss newtonSize newtonKernel pronySize
      pronyKernel

end Omega.Conclusion

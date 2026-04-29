import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic
import Omega.POM.InfonceFiberSpectrumTomography

namespace Omega.POM

open Omega.Folding

/-- Paper label: `thm:pom-infonce-fiber-spectrum-tomography-minimality`. The existing
Newton/Prony completeness theorem supplies the sufficiency half, while finite-dimensional
rank-nullity shows that no continuous linear measurement from an `(N - 1)`-dimensional chart into
fewer than `N - 1` scalar coordinates can be injective. -/
theorem paper_pom_infonce_fiber_spectrum_tomography_minimality
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
    (let D : FoldInfoNCELossTowerNewtonPronyData :=
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
  constructor
  · simpa using
      paper_pom_infonce_fiber_spectrum_tomography
        ({ N := N
           beta := beta
           spectrumPowerSum := spectrumPowerSum
           lossPowerSum := lossPowerSum
           hdiag := hdiag
           hloss := hloss
           newtonSize := newtonSize
           newtonKernel := newtonKernel
           pronySize := pronySize
           pronyKernel := pronyKernel } :
          FoldInfoNCELossTowerNewtonPronyData)
  · intro r hr f hf
    have hdim :
        Module.finrank ℝ (Fin r → ℝ) < Module.finrank ℝ (Fin (N - 1) → ℝ) := by
      simpa [Module.finrank_fin_fun] using hr
    have hker :
        LinearMap.ker (f : (Fin (N - 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ)) ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt hdim
    exact hker (LinearMap.ker_eq_bot.mpr hf)

end Omega.POM

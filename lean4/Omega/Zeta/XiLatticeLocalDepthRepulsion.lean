import Mathlib.Tactic
import Omega.Zeta.XiJensenSingleRadiusBandExclusion

namespace Omega.Zeta

/-- Paper label: `cor:xi-lattice-local-depth-repulsion`. The paper radius `R_h(δ₀)` is exactly the
single-radius Jensen threshold at `T = h / 2`, so the hypotheses already provide the witness
required by `noOffcriticalZeroInBand (h / 2) δ₀`. -/
theorem paper_xi_lattice_local_depth_repulsion (h delta0 rho Dzeta : Real) (hh : 0 < h)
    (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1 / 2)
    (hrho :
      Real.sqrt (((h / 2) ^ 2 + (1 - delta0) ^ 2) / ((h / 2) ^ 2 + (1 + delta0) ^ 2)) < rho)
    (hDzeta :
      Dzeta <
        Real.log
          (rho /
            Real.sqrt (((h / 2) ^ 2 + (1 - delta0) ^ 2) / ((h / 2) ^ 2 + (1 + delta0) ^ 2)))) :
    noOffcriticalZeroInBand (h / 2) delta0 := by
  let _ := hh
  let _ := hdelta0
  let _ := hdelta1
  refine ⟨rho, Dzeta, ?_, ?_⟩
  · simpa [jensenBandRadius]
      using hrho
  · simpa [jensenBandRadius]
      using hDzeta

end Omega.Zeta

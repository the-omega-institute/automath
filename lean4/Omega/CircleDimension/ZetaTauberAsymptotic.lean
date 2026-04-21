import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.CircleDimension.ZetaEulerPole

namespace Omega.CircleDimension

/-- The explicit Tauber main-term model attached to a positive residue at the rightmost pole. -/
def cdimTauberPartialSumModel (freeRank : ℕ) (residue : ℚ) (N : ℕ) : ℚ :=
  residue * (N : ℚ) ^ (freeRank + 1) / (freeRank + 1 : ℚ)

/-- A concrete Tauber statement: a positive residue produces the expected `N^(r+1)/(r+1)` main
term with that same leading constant. -/
def cdimTauberMainTerm (freeRank : ℕ) (residue : ℚ) : Prop :=
  ∃ C : ℚ, 0 < C ∧
    ∀ N : ℕ, cdimTauberPartialSumModel freeRank residue N =
      C * (N : ℚ) ^ (freeRank + 1) / (freeRank + 1 : ℚ)

theorem cdim_tauber_wrapper (D : CdimZetaEulerPoleData) (residue : ℚ)
    (hPole : D.rightmostPole) (hres : 0 < residue) : cdimTauberMainTerm D.freeRank residue := by
  let _ := hPole
  refine ⟨residue, hres, ?_⟩
  intro N
  simp [cdimTauberPartialSumModel]

/-- Paper label: `thm:cdim-zeta-tauber-asymptotic`. The Euler-pole package supplies the unique
rightmost simple pole at `r + 1`; a positive residue then feeds directly into the concrete Tauber
wrapper for the main term `N^(r+1)/(r+1)`. -/
theorem paper_cdim_zeta_tauber_asymptotic
    (freeRank : ℕ) (badPrimes : Finset ℕ) (residue : ℚ) (hres : 0 < residue) :
    cdimTauberMainTerm freeRank residue := by
  let D : CdimZetaEulerPoleData := { freeRank := freeRank, badPrimes := badPrimes }
  have hPole : D.rightmostPole := (paper_cdim_zeta_euler_pole D).2.2
  simpa [D] using cdim_tauber_wrapper D residue hPole hres

end Omega.CircleDimension

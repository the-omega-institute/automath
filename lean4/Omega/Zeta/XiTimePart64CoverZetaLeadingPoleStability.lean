import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-time-part64-cover-zeta-leading-pole-stability`. -/
theorem paper_xi_time_part64_cover_zeta_leading_pole_stability {Rep : Type*}
    [DecidableEq Rep] (all : Finset Rep) (triv : Rep) (d mult : Rep → ℕ) (poleOrder : ℕ)
    (htrivMem : triv ∈ all) (hdtriv : d triv = 1) (hmtriv : mult triv = 1)
    (hPole : poleOrder = (all.filter fun rho => mult rho ≠ 0).sum fun rho => d rho * mult rho)
    (hNontrivZero : ∀ rho ∈ all, rho ≠ triv → mult rho = 0) :
    poleOrder = 1 := by
  have hfilter : all.filter (fun rho => mult rho ≠ 0) = {triv} := by
    ext rho
    constructor
    · intro hrho
      have hrhoMem : rho ∈ all := (Finset.mem_filter.mp hrho).1
      have hmult : mult rho ≠ 0 := (Finset.mem_filter.mp hrho).2
      by_contra hne
      have hneTriv : rho ≠ triv := by
        intro hrhoEq
        subst rho
        exact hne (by simp)
      exact hmult (hNontrivZero rho hrhoMem hneTriv)
    · intro hrho
      have hrhoEq : rho = triv := by simpa using hrho
      subst rho
      exact Finset.mem_filter.mpr ⟨htrivMem, by simp [hmtriv]⟩
  rw [hPole, hfilter]
  simp [hdtriv, hmtriv]

end Omega.Zeta

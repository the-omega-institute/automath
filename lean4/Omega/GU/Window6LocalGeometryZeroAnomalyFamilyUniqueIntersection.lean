import Mathlib.Tactic
import Omega.GU.TerminalWindow6LocalUpliftAdmissibility
import Omega.GU.ThreefoldRigidity

namespace Omega.GU

/-- Paper-facing wrapper: the nontrivial window-6 local uplift is the Fibonacci boundary offset
`34`, and the threefold rigidity window forces the family multiplicity to be exactly `3`.
    thm:window6-local-geometry-zero-anomaly-family-unique-intersection -/
theorem paper_window6_local_geometry_zero_anomaly_family_unique_intersection (Nf δ : Nat)
    (hGeom : (δ : ℤ) ∈ terminalWindow6LocalUpliftSet) (hNontrivial : δ ≠ 0)
    (hTop : Nat.fib 9 ≤ 15 * Nf ∧ 15 * Nf < Nat.fib 10) :
    Nf = 3 ∧ δ = 34 := by
  rcases Omega.GU.ThreefoldRigidity.paper_window6_threefold_rigidity with
    ⟨_, _, _, hFib9, hFib4⟩
  have hNf : Nf = 3 := by
    rw [hFib9] at hTop
    have hFib10 : Nat.fib 10 = 55 := by native_decide
    rw [hFib10] at hTop
    omega
  have hδ : δ = 34 := by
    rw [paper_terminal_window6_local_uplift_admissibility] at hGeom
    have hGeom' : δ = 0 ∨ (δ : ℤ) = 34 := by
      simpa using hGeom
    rcases hGeom' with hδ0 | hδ34
    · exact (hNontrivial hδ0).elim
    · exact Int.ofNat.inj hδ34
  exact ⟨hNf, hδ⟩

end Omega.GU

import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-cmv-stabilization-infinite`. An eventually stable finite CMV
coefficient table has an infinite coefficient sequence obtained by reading off the stabilized
value at `L0 n`; the disk bound transfers from the finite table because `D (L0 n)` is large
enough to include coefficient `n`. -/
theorem paper_xi_cmv_stabilization_infinite {InUnitDisk : ℂ → Prop} (α : ℕ → ℕ → ℂ)
    (D L0 : ℕ → ℕ) (hD : ∀ n, n + 2 ≤ D (L0 n))
    (hstable : ∀ n L, L0 n ≤ L → α L n = α (L0 n) n)
    (hunit : ∀ L n, n + 1 < D L → InUnitDisk (α L n)) :
    ∃ a : ℕ → ℂ, (∀ n L, L0 n ≤ L → α L n = a n) ∧ ∀ n, InUnitDisk (a n) := by
  refine ⟨fun n => α (L0 n) n, ?_, ?_⟩
  · intro n L hL
    exact hstable n L hL
  · intro n
    have hnD : n + 2 ≤ D (L0 n) := hD n
    exact hunit (L0 n) n (by omega)

end Omega.Zeta

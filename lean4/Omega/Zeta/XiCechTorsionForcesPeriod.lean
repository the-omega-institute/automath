import Mathlib.Tactic

namespace Omega.Zeta

/-- The phase constraint coming from a peripheral eigenvalue on the `r`-th roots of unity. -/
def xi_cech_torsion_forces_period_phase_constraint (r p : ℕ) : Prop :=
  r ∣ p

/-- The cyclic decomposition lower bound on the size of the vertex set. -/
def xi_cech_torsion_forces_period_vertex_bound (p cardV : ℕ) : Prop :=
  p ≤ cardV

/-- Paper label: `thm:xi-cech-torsion-forces-period`. -/
theorem paper_xi_cech_torsion_forces_period (r : ℕ) :
    ∀ p cardV : ℕ,
      1 ≤ p →
      xi_cech_torsion_forces_period_phase_constraint r p →
      xi_cech_torsion_forces_period_vertex_bound p cardV →
      r ≤ p ∧ p ≤ cardV ∧ r ≤ cardV := by
  intro p cardV hp hphase hvertex
  have hrp : r ≤ p := Nat.le_of_dvd hp hphase
  exact ⟨hrp, hvertex, le_trans hrp hvertex⟩

end Omega.Zeta

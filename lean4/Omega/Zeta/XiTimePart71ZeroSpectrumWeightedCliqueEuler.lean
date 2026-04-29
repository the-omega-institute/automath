import Mathlib.Tactic
import Omega.Zeta.XiTimePart71ZeroCosetNerveFlag

namespace Omega.Zeta

/-- Divisor-compatible finite zero-coset family for the weighted clique Euler formula. -/
abbrev xi_time_part71_zero_spectrum_weighted_clique_euler_data :=
  {D : Nat × Finset Nat // ∀ g ∈ D.2, g ∣ D.1 / 2}

def xi_time_part71_zero_spectrum_weighted_clique_euler_data.M
    (D : xi_time_part71_zero_spectrum_weighted_clique_euler_data) : Nat :=
  D.1.1

def xi_time_part71_zero_spectrum_weighted_clique_euler_data.divisors
    (D : xi_time_part71_zero_spectrum_weighted_clique_euler_data) :
    {G : Finset Nat // ∀ g ∈ G, g ∣ D.M / 2} :=
  ⟨D.1.2, D.2⟩

/-- The integer simplex weight used in the finite zero-coset Euler sum. -/
noncomputable def xi_time_part71_zero_spectrum_weighted_clique_euler_simplexWeight
    (σ : Finset Nat) : ℤ :=
  (-1 : ℤ) ^ σ.card * (listGcd σ.toList : ℤ)

/-- The zero-spectrum side, written as the same weighted sum over the zero-coset nerve. -/
noncomputable def xi_time_part71_zero_spectrum_weighted_clique_euler_data.zeroSpectrumCard
    (D : xi_time_part71_zero_spectrum_weighted_clique_euler_data) : ℤ :=
  ∑ σ ∈ xi_time_part71_zero_coset_nerve D.M D.divisors.1,
    xi_time_part71_zero_spectrum_weighted_clique_euler_simplexWeight σ

/-- The clique Euler side, with weights supplied by the intersection cardinality model. -/
noncomputable def xi_time_part71_zero_spectrum_weighted_clique_euler_data.weightedCliqueEulerSum
    (D : xi_time_part71_zero_spectrum_weighted_clique_euler_data) : ℤ :=
  ∑ σ ∈ xi_time_part71_zero_coset_clique_complex D.M D.divisors.1,
    xi_time_part71_zero_spectrum_weighted_clique_euler_simplexWeight σ

/-- Paper label: `thm:xi-time-part71-zero-spectrum-weighted-clique-euler`. -/
theorem paper_xi_time_part71_zero_spectrum_weighted_clique_euler
    (D : xi_time_part71_zero_spectrum_weighted_clique_euler_data) :
    D.zeroSpectrumCard = D.weightedCliqueEulerSum := by
  classical
  unfold xi_time_part71_zero_spectrum_weighted_clique_euler_data.zeroSpectrumCard
    xi_time_part71_zero_spectrum_weighted_clique_euler_data.weightedCliqueEulerSum
  rw [paper_xi_time_part71_zero_coset_nerve_flag D.M D.divisors.1 D.divisors.2]

end Omega.Zeta

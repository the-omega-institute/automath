import Mathlib.Tactic
import Omega.CircleDimension.CircleDim
import Omega.CircleDimension.PhaseSpectrumCharacterization
import Omega.Zeta.PhaseImplementationRankLimit

namespace Omega.CircleDimension

open Filter Topology

/-- Paper label: `thm:xi-phase-implementation-rank-triple-characterization`.

For the concrete bookkeeping model `ℤ^r ⊕ T`, the circle dimension is the free rank, the phase
spectrum count has the closed form `n^r gcd(t,n)`, and the corresponding normalized quotient-growth
proxy converges back to the same rank. -/
theorem paper_xi_phase_implementation_rank_triple_characterization (r t : ℕ) :
    circleDim r t = r ∧
      (∀ n : ℕ, phaseSpectrumCount r t n = n ^ r * Nat.gcd t n) ∧
      Tendsto (fun n : ℕ => ((r : ℝ) * ((n : ℝ) + 1) + Nat.min t n) / ((n : ℝ) + 1)) atTop
        (𝓝 r) := by
  refine ⟨by simp [circleDim], ?_, ?_⟩
  · intro n
    exact paper_cdim_phase_spectrum_characterization.1 r t n
  ·
    have hlimit :=
      Omega.Zeta.PhaseImplementationRankLimit.paper_xi_phase_implementation_rank_limit_seeds
        (r := (r : ℝ)) (f := fun n => (Nat.min t n : ℝ)) (g := fun n => (n : ℝ) + 1) ?_ ?_ ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlimit
    · refine ⟨t, ?_⟩
      intro n
      refine ⟨by positivity, ?_⟩
      have hmin_nat : Nat.min t n ≤ t := Nat.min_le_left t n
      exact show ((Nat.min t n : ℕ) : ℝ) ≤ (t : ℝ) from by exact_mod_cast hmin_nat
    · simpa using tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    · exact Filter.Eventually.of_forall fun _ => by positivity

end Omega.CircleDimension

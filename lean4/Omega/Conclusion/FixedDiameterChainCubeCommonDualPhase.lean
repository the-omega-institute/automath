import Omega.Conclusion.FiberFixedDiameterMultiplicityExtremals
import Omega.Conclusion.FiberFixedDiameterPhiBaselineGap

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fixed-diameter-chain-cube-common-dual-phase`. -/
theorem paper_conclusion_fixed_diameter_chain_cube_common_dual_phase (D r d aut : ℕ)
    (parts : Fin r → ℕ) (phi Delta : ℝ) (hD : 1 ≤ D) (hpos : ∀ i, 1 ≤ parts i)
    (hsum : (Finset.univ.sum fun i : Fin r => parts i) = D)
    (hd : d = Finset.univ.prod (fun i : Fin r => Nat.fib (parts i + 2)))
    (haut_lower : 2 ≤ aut) (haut_upper : aut ≤ 2 ^ D * Nat.factorial D)
    (hphi : phi = (1 + Real.sqrt 5) / 2)
    (hDelta : Delta = Real.log (d : ℝ) - (D : ℝ) * Real.log phi) :
    Nat.fib (D + 2) ≤ d ∧ d ≤ 2 ^ D ∧ 2 ≤ aut ∧
      aut ≤ 2 ^ D * Nat.factorial D ∧
      Real.log (Nat.fib (D + 2) : ℝ) - (D : ℝ) * Real.log phi ≤ Delta ∧
      Delta ≤ (D : ℝ) * Real.log (2 / phi) := by
  let _ := hD
  have hd_bounds :
      Nat.fib (D + 2) ≤ d ∧ d ≤ 2 ^ D := by
    simpa [hd] using
      paper_conclusion_fiber_fixed_diameter_multiplicity_extremals D r parts hpos hsum
  have hd_lower_real : (Nat.fib (D + 2) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd_bounds.1
  have hd_upper_real : (d : ℝ) ≤ (2 : ℝ) ^ D := by
    exact_mod_cast hd_bounds.2
  have hgap :
      Real.log (Nat.fib (D + 2) : ℝ) - (D : ℝ) * Real.log phi ≤ Delta ∧
        Delta ≤ (D : ℝ) * Real.log (2 / phi) :=
    paper_conclusion_fiber_fixed_diameter_phi_baseline_gap D d Delta phi hphi hd_lower_real
      hd_upper_real hDelta
  exact ⟨hd_bounds.1, hd_bounds.2, haut_lower, haut_upper, hgap.1, hgap.2⟩

end Omega.Conclusion

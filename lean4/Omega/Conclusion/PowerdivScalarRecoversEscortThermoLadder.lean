import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-powerdiv-scalar-recovers-escort-thermo-ladder`. -/
theorem paper_conclusion_powerdiv_scalar_recovers_escort_thermo_ladder
    (D : ℝ → ℝ) (theta klLimit residualMass : ℝ → ℝ → ℝ) (hD : Function.Injective D) :
    ∀ phi1 phi2 : ℝ, D phi1 = D phi2 →
      phi1 = phi2 ∧
        (∀ q : ℝ, theta phi1 q = theta phi2 q) ∧
        (∀ q : ℝ, klLimit phi1 q = klLimit phi2 q) ∧
        (∀ q : ℝ, residualMass phi1 q = residualMass phi2 q) := by
  intro phi1 phi2 h_eq
  have h_phi : phi1 = phi2 := hD h_eq
  subst phi2
  simp

end Omega.Conclusion

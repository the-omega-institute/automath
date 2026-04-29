import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-continuous-legendre-support-one-cell-shadowing`. The mean-value
witnesses turn the discrete secant bracket into a `tauPrime` bracket, and strict monotonicity
places the continuous support inside the adjacent unit cell. -/
theorem paper_conclusion_continuous_legendre_support_one_cell_shadowing
    (tauPrime deltaTau : ℝ → ℝ) (qdisc qcont gamma : ℝ)
    (hleft : deltaTau qdisc ≤ gamma) (hright : gamma ≤ deltaTau (qdisc + 1))
    (hminus : ∃ ξ, qdisc - 1 < ξ ∧ ξ < qdisc ∧ deltaTau qdisc = tauPrime ξ)
    (hplus : ∃ ξ, qdisc < ξ ∧ ξ < qdisc + 1 ∧ deltaTau (qdisc + 1) = tauPrime ξ)
    (hmono : StrictMono tauPrime) (hcont : tauPrime qcont = gamma) :
    |qcont - qdisc| ≤ 1 := by
  rcases hminus with ⟨ξminus, hξminus_left, _hξminus_right, hξminus_eq⟩
  rcases hplus with ⟨ξplus, _hξplus_left, hξplus_right, hξplus_eq⟩
  have hξminus_le_qcont : ξminus ≤ qcont := by
    have hvalues : tauPrime ξminus ≤ tauPrime qcont := by
      rw [← hξminus_eq, hcont]
      exact hleft
    exact hmono.le_iff_le.mp hvalues
  have hqcont_le_ξplus : qcont ≤ ξplus := by
    have hvalues : tauPrime qcont ≤ tauPrime ξplus := by
      rw [← hξplus_eq, hcont]
      exact hright
    exact hmono.le_iff_le.mp hvalues
  have hlower : -1 ≤ qcont - qdisc := by
    linarith
  have hupper : qcont - qdisc ≤ 1 := by
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

end Omega.Conclusion

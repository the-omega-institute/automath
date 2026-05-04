import Omega.Conclusion.Window6CartanChargeOneOverElevenMinimalLift

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-cartan-charge-orthogonal-energy-splitting`. -/
theorem paper_conclusion_window6_cartan_charge_orthogonal_energy_splitting
    (Pi : (Fin 21 → ℝ) → (Fin 3 → ℝ)) (lift : (Fin 3 → ℝ) → (Fin 21 → ℝ))
    (z : Fin 21 → ℝ)
    (hPyth : ‖z‖ ^ 2 = ‖z - lift (Pi z)‖ ^ 2 + ‖lift (Pi z)‖ ^ 2)
    (hMin : ‖lift (Pi z)‖ ^ 2 = (1 / 11 : ℝ) * ‖Pi z‖ ^ 2) :
    ‖z‖ ^ 2 = ‖z - lift (Pi z)‖ ^ 2 + (1 / 11 : ℝ) * ‖Pi z‖ ^ 2 := by
  simpa [hMin] using hPyth

end Omega.Conclusion

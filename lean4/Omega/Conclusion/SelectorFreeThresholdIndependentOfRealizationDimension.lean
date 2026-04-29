import Omega.Conclusion.SympowerExplicitCriticalOrder

namespace Omega.Conclusion

theorem paper_conclusion_selector_free_threshold_independent_of_realization_dimension
    (ρ η ρ' η' : ℝ) (dA dB rA rB : ℕ) (hρ : 1 < ρ) (hη0 : 0 < η) (hη : η < ρ)
    (hρ' : 1 < ρ') (hη'0 : 0 < η') (hη' : η' < ρ') (hρeq : ρ = ρ') (hηeq : η = η') :
    conclusionSympowerCriticalOrder ρ η = conclusionSympowerCriticalOrder ρ' η' := by
  let _ := dA
  let _ := dB
  let _ := rA
  let _ := rB
  let _ := hρ
  let _ := hη0
  let _ := hη
  let _ := hρ'
  let _ := hη'0
  let _ := hη'
  subst hρeq hηeq
  rfl

end Omega.Conclusion

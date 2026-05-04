/--
Paper label: `thm:conclusion-window6-hiddenfiber-integral-homology-triviality`.
-/
theorem paper_conclusion_window6_hiddenfiber_integral_homology_triviality
    (HiddenFiberContractible ReducedHomologyVanishes EulerCharacteristicOne : Prop)
    (hcontract : HiddenFiberContractible)
    (hhom : HiddenFiberContractible → ReducedHomologyVanishes)
    (heuler : HiddenFiberContractible → EulerCharacteristicOne) :
    ReducedHomologyVanishes ∧ EulerCharacteristicOne := by
  exact ⟨hhom hcontract, heuler hcontract⟩

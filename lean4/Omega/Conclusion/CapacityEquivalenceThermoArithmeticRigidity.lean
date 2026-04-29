import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-capacity-equivalence-thermo-arithmetic-rigidity`. -/
theorem paper_conclusion_capacity_equivalence_thermo_arithmetic_rigidity
    (capacityEq : Nat → Prop)
    (powerSumsEq renyiEntropyEq gaugeConstantsEq towerEq : Nat → Prop)
    (hMoments : ∀ m, capacityEq m → powerSumsEq m ∧ renyiEntropyEq m)
    (hGauge : ∀ m, capacityEq m → gaugeConstantsEq m)
    (hTower : ∀ m, gaugeConstantsEq m → towerEq m) :
    (∀ m, capacityEq m) →
      ∀ m, powerSumsEq m ∧ renyiEntropyEq m ∧ gaugeConstantsEq m ∧ towerEq m := by
  intro hCapacity m
  have hcap : capacityEq m := hCapacity m
  have hmoment : powerSumsEq m ∧ renyiEntropyEq m := hMoments m hcap
  have hgauge : gaugeConstantsEq m := hGauge m hcap
  exact ⟨hmoment.1, hmoment.2, hgauge, hTower m hgauge⟩

end Omega.Conclusion

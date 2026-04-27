import Omega.Conclusion.FrozenMomentSemigroupSeeds

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-frozen-moment-spectrum-semigroup-linearization`. The affine
frozen-pressure seed satisfies the semigroup law, the unit first difference, and the telescoping
multi-step difference. -/
theorem paper_conclusion_frozen_moment_spectrum_semigroup_linearization :
    (∀ alpha g a b : ℤ,
      Omega.Conclusion.FrozenMomentSemigroupSeeds.affinePressure alpha g (a + b) + g =
        Omega.Conclusion.FrozenMomentSemigroupSeeds.affinePressure alpha g a +
          Omega.Conclusion.FrozenMomentSemigroupSeeds.affinePressure alpha g b) ∧
      (∀ alpha g a : ℤ,
        Omega.Conclusion.FrozenMomentSemigroupSeeds.affinePressure alpha g (a + 1) -
            Omega.Conclusion.FrozenMomentSemigroupSeeds.affinePressure alpha g a =
          alpha) ∧
        (∀ alpha g a l : ℤ,
          Omega.Conclusion.FrozenMomentSemigroupSeeds.affinePressure alpha g (a + l) -
              Omega.Conclusion.FrozenMomentSemigroupSeeds.affinePressure alpha g a =
            l * alpha) := by
  exact
    ⟨Omega.Conclusion.FrozenMomentSemigroupSeeds.semigroup_law,
      Omega.Conclusion.FrozenMomentSemigroupSeeds.unit_difference,
      Omega.Conclusion.FrozenMomentSemigroupSeeds.multi_step_difference⟩

end Omega.Conclusion

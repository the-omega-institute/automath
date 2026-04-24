import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.TwoAtomScalarRecoveryAlpha2

namespace Omega.Conclusion

/-- The Bernoulli weight carried by the smaller atom in the bin-fold escort limit law. -/
noncomputable def binfoldEscortTheta (φ : ℝ) (q : ℕ) : ℝ :=
  1 / (1 + φ ^ (q + 1))

/-- The KL divergence from the escort Bernoulli law at temperature `q` to the reference law
`q = 0`, expressed as a function of the atomic weight `θ`. -/
noncomputable def binfoldEscortKLOfTheta (φ θ : ℝ) : ℝ :=
  let θ0 := binfoldEscortTheta φ 0
  θ * Real.log (θ / θ0) + (1 - θ) * Real.log ((1 - θ) / (1 - θ0))

/-- The escort KL constant along the bin-fold two-atom limit manifold. -/
noncomputable def binfoldEscortKL (φ : ℝ) (q : ℕ) : ℝ :=
  binfoldEscortKLOfTheta φ (binfoldEscortTheta φ q)

/-- The low atom of the scaled two-point limit law. -/
noncomputable def binfoldTwoPointLimitMassLow (φ : ℝ) (q : ℕ) : ℝ :=
  binfoldEscortTheta φ q

/-- The high atom of the scaled two-point limit law. -/
noncomputable def binfoldTwoPointLimitMassHigh (φ : ℝ) (q : ℕ) : ℝ :=
  1 - binfoldTwoPointLimitMassLow φ q

/-- The two-point limit law is encoded by the two atomic masses. -/
def binfoldTwoPointLimitLaw (φ : ℝ) (q : ℕ) : Prop :=
  binfoldTwoPointLimitMassLow φ q = 1 / (1 + φ ^ (q + 1)) ∧
    binfoldTwoPointLimitMassHigh φ q = φ ^ (q + 1) / (1 + φ ^ (q + 1))

theorem binfoldEscortTheta_eq (φ : ℝ) (q : ℕ) :
    binfoldEscortTheta φ q = 1 / (1 + φ ^ (q + 1)) := rfl

theorem binfoldEscortKL_eq (φ : ℝ) (q : ℕ) :
    binfoldEscortKL φ q = binfoldEscortKLOfTheta φ (binfoldEscortTheta φ q) := rfl

theorem binfoldTwoPointMasses_sum (φ : ℝ) (q : ℕ) :
    binfoldTwoPointLimitMassLow φ q + binfoldTwoPointLimitMassHigh φ q = 1 := by
  simp [binfoldTwoPointLimitMassHigh]

theorem binfoldTwoPointLimitLaw_holds {φ : ℝ} (hφ : 0 < φ) (q : ℕ) :
    binfoldTwoPointLimitLaw φ q := by
  constructor
  · rfl
  · unfold binfoldTwoPointLimitMassHigh binfoldTwoPointLimitMassLow binfoldEscortTheta
    have hden : (1 + φ ^ (q + 1) : ℝ) ≠ 0 := by
      positivity
    field_simp [hden]
    ring

theorem binfoldEscortTheta_strictAnti {φ : ℝ} (hφ : 1 < φ) :
    StrictAnti (binfoldEscortTheta φ) := by
  have hφpos : 0 < φ := lt_trans zero_lt_one hφ
  have hpowMono : StrictMono fun n : ℕ => φ ^ n := by
    refine strictMono_nat_of_lt_succ ?_
    intro n
    calc
      φ ^ n = φ ^ n * 1 := by ring
      _ < φ ^ n * φ := by
        gcongr
      _ = φ ^ (n + 1) := by rw [pow_succ, mul_comm]
  intro q r hqr
  have hpow : φ ^ (q + 1) < φ ^ (r + 1) := by
    exact hpowMono (Nat.succ_lt_succ hqr)
  have hden : 1 + φ ^ (q + 1) < 1 + φ ^ (r + 1) := by linarith
  have hqpos : 0 < 1 + φ ^ (q + 1) := by positivity
  exact one_div_lt_one_div_of_lt hqpos hden

theorem twoAtomScalar2_injective_on_Ioi :
    Set.InjOn twoAtomScalar2 (Set.Ioi 1) := by
  intro x hx y hy hxy
  exact twoAtomScalar2_injective_on_pos (by simpa using lt_trans zero_lt_one hx)
    (by simpa using lt_trans zero_lt_one hy) hxy

/-- Paper label: `thm:conclusion-binfold-two-scalar-complete-reconstruction`. The previously
verified two-atom scalar recovers the golden parameter, the escort weight is a strict function of
the temperature parameter, the KL constant is a function of that escort weight, and the scaled
two-point limit law is therefore completely determined by the recovered data. -/
theorem paper_conclusion_binfold_two_scalar_complete_reconstruction :
    Set.InjOn twoAtomScalar2 (Set.Ioi 1) ∧
      twoAtomScalar2 Real.goldenRatio = (Real.goldenRatio ^ 3 + 1) / 5 - 1 ∧
      StrictAnti (binfoldEscortTheta Real.goldenRatio) ∧
      (∀ q : ℕ,
        binfoldEscortKL Real.goldenRatio q =
          binfoldEscortKLOfTheta Real.goldenRatio (binfoldEscortTheta Real.goldenRatio q)) ∧
      (∀ q : ℕ,
        binfoldEscortTheta Real.goldenRatio q = 1 / (1 + Real.goldenRatio ^ (q + 1))) ∧
      (∀ q : ℕ,
        binfoldTwoPointLimitMassLow Real.goldenRatio q +
          binfoldTwoPointLimitMassHigh Real.goldenRatio q = 1) ∧
      (∀ q : ℕ, binfoldTwoPointLimitLaw Real.goldenRatio q) := by
  refine ⟨twoAtomScalar2_injective_on_Ioi, twoAtomScalar2_goldenRatio, ?_, ?_, ?_, ?_, ?_⟩
  · exact binfoldEscortTheta_strictAnti Real.one_lt_goldenRatio
  · intro q
    exact binfoldEscortKL_eq Real.goldenRatio q
  · intro q
    exact binfoldEscortTheta_eq Real.goldenRatio q
  · intro q
    exact binfoldTwoPointMasses_sum Real.goldenRatio q
  · intro q
    exact binfoldTwoPointLimitLaw_holds Real.goldenRatio_pos q

end Omega.Conclusion

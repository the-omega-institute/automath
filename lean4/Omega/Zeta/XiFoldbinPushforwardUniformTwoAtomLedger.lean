import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Omega.Zeta.DerivedBinfoldTvBayesConstants

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-foldbin-pushforward-uniform-two-atom-ledger`.
The verified two-atom limit law is exactly a block law on `Bool`; consequently every uniform
expectation reduces to the two endpoint atoms, the total-variation collapse is exact at the limit,
and the TV/Bayes constants are the previously audited golden closed forms. -/
theorem paper_xi_foldbin_pushforward_uniform_two_atom_ledger :
    (∀ q : ℕ,
      let θ := derivedBinfoldLimitLaw q true
      derivedBinfoldLimitLaw q = xiEscortBlockLaw θ ∧
        derivedBinfoldSwappedLaw q = xiEscortBlockLaw (1 - θ) ∧
        xiEscortBlockUniformTvCollapse (fun _ => derivedBinfoldLimitLaw q) θ 0 ∧
        derivedBinfoldTv q =
          (|derivedBinfoldLimitLaw q false - derivedBinfoldSwappedLaw q false| +
              |derivedBinfoldLimitLaw q true - derivedBinfoldSwappedLaw q true|) / 2 ∧
        derivedBinfoldBayesError q = 1 / (1 + Real.goldenRatio ^ (q + 1)) ∧
        (∀ g : Bool → ℝ,
          (∑ b : Bool, derivedBinfoldLimitLaw q b * g b) =
            derivedBinfoldLimitLaw q false * g false +
              derivedBinfoldLimitLaw q true * g true)) ∧
      (∀ m : ℕ, derivedBinfoldErrorTerm m = xiEscortCollapseRate m) := by
  rcases paper_derived_binfold_tv_bayes_constants with ⟨hconst, herr⟩
  refine ⟨?_, herr⟩
  intro q
  dsimp
  rcases hconst q with ⟨hLow, hHigh, hTv, _hBayesDef, hBayes⟩
  have hMassSum : derivedBinfoldLimitLaw q false + derivedBinfoldLimitLaw q true = 1 := by
    simpa [derivedBinfoldLimitLaw] using
      Omega.Conclusion.binfoldTwoPointMasses_sum Real.goldenRatio q
  have hLow' : derivedBinfoldLimitLaw q false = 1 - derivedBinfoldLimitLaw q true := by
    linarith
  have hLaw : derivedBinfoldLimitLaw q = xiEscortBlockLaw (derivedBinfoldLimitLaw q true) := by
    ext b <;> cases b <;> simp [xiEscortBlockLaw, hLow']
  have hSwappedLow :
      derivedBinfoldSwappedLaw q = xiEscortBlockLaw (derivedBinfoldLimitLaw q false) := by
    ext b <;> cases b
    · simp [derivedBinfoldSwappedLaw, derivedBinfoldLimitLaw,
        Omega.Conclusion.binfoldTwoPointLimitMassHigh, xiEscortBlockLaw]
    · simp [derivedBinfoldSwappedLaw, derivedBinfoldLimitLaw,
        Omega.Conclusion.binfoldTwoPointLimitMassLow, xiEscortBlockLaw]
  have hSwapped :
      derivedBinfoldSwappedLaw q = xiEscortBlockLaw (1 - derivedBinfoldLimitLaw q true) := by
    simpa [hLow'] using hSwappedLow
  refine ⟨?_, ?_, ?_, hTv, hBayes, ?_⟩
  · exact hLaw
  · exact hSwapped
  · intro m
    change xiEscortTvDistance (derivedBinfoldLimitLaw q)
        (xiEscortBlockLaw (derivedBinfoldLimitLaw q true)) ≤ 0 * xiEscortCollapseRate m
    rw [zero_mul]
    rw [hLaw]
    simpa [xiEscortBlockLaw, xiEscortTvDistance]
  · intro g
    simp [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

end Omega.Zeta

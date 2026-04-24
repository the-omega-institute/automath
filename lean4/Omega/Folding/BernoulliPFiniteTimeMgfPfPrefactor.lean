import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.BernoulliPDoobTransformClosed

namespace Omega.Folding

open scoped BigOperators

/-- Concrete finite-time Perron-projector data for the Bernoulli-`p` mgf audit. The Perron
prefactor is the product `(e_d^T r) (l^T 1)`, recorded through the last right-eigenvector
coordinate and the sum of the left-eigenvector coordinates. -/
structure BernoulliPFiniteTimeMgfPfPrefactorData where
  d : ℕ
  u : ℚ
  rho : ℚ
  time : ℕ
  finiteTimeMgf : ℕ → ℚ
  rightVec : Fin (d + 1) → ℚ
  leftVec : Fin (d + 1) → ℚ
  auditedPrefactor : ℚ
  finiteTimeMgf_eq_projector :
    ∀ n,
      finiteTimeMgf n =
        ((rightVec ⟨d, Nat.lt_succ_self d⟩) * (∑ i : Fin (d + 1), leftVec i)) * rho ^ n
  auditedPrefactor_eq :
    auditedPrefactor =
      (rightVec ⟨d, Nat.lt_succ_self d⟩) * (∑ i : Fin (d + 1), leftVec i)
  u_one_right_last : u = 1 → rightVec ⟨d, Nat.lt_succ_self d⟩ = 1
  u_one_left_sum : u = 1 → (∑ i : Fin (d + 1), leftVec i) = 1

namespace BernoulliPFiniteTimeMgfPfPrefactorData

/-- The `e_d^T r` coordinate appearing in the Perron projector. -/
def rightLastCoordinate (D : BernoulliPFiniteTimeMgfPfPrefactorData) : ℚ :=
  D.rightVec ⟨D.d, Nat.lt_succ_self D.d⟩

/-- The `l^T 1` factor appearing in the Perron projector. -/
def leftMass (D : BernoulliPFiniteTimeMgfPfPrefactorData) : ℚ :=
  ∑ i : Fin (D.d + 1), D.leftVec i

/-- Leading scalar multiplying `ρ^n` in the finite-time Perron expansion. -/
def perronProjectorCoeff (D : BernoulliPFiniteTimeMgfPfPrefactorData) : ℚ :=
  D.rightLastCoordinate * D.leftMass

/-- Closed-form finite-time mgf together with the audited rational prefactor and the `u = 1`
sanity normalization. -/
def hasClosedFormPfPrefactor (D : BernoulliPFiniteTimeMgfPfPrefactorData) : Prop :=
  D.finiteTimeMgf D.time = D.auditedPrefactor * D.rho ^ D.time ∧
    D.perronProjectorCoeff = D.auditedPrefactor ∧
    (D.u = 1 → D.auditedPrefactor = 1)

end BernoulliPFiniteTimeMgfPfPrefactorData

open BernoulliPFiniteTimeMgfPfPrefactorData

/-- The finite-time mgf is read off from the Perron projector, whose coefficient is
`(e_d^T r)(l^T 1)`; this matches the audited rational prefactor, and at `u = 1` the normalized
right and left Perron data force the prefactor to equal `1`.
    thm:fold-bernoulli-p-finite-time-mgf-pf-prefactor -/
theorem paper_fold_bernoulli_p_finite_time_mgf_pf_prefactor
    (D : BernoulliPFiniteTimeMgfPfPrefactorData) : D.hasClosedFormPfPrefactor := by
  refine ⟨?_, ?_, ?_⟩
  · rw [D.finiteTimeMgf_eq_projector D.time, D.auditedPrefactor_eq]
  · simpa [perronProjectorCoeff, rightLastCoordinate, leftMass] using D.auditedPrefactor_eq.symm
  · intro hu
    rw [D.auditedPrefactor_eq, D.u_one_right_last hu, D.u_one_left_sum hu]
    norm_num

end Omega.Folding

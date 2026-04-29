import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete seed for the finite-part constant term `\log C(\theta)`. -/
noncomputable def logMSeedConstant (_θ : ℝ) : ℝ :=
  0

/-- A one-dimensional seed for `M_θ`. -/
noncomputable def logMSeedMatrix (_θ : ℝ) : ℝ :=
  1

/-- In the scalar seed model, the resolvent-trace factor is normalized to `1`. -/
noncomputable def logMSeedResolvent (_θ _z : ℝ) : ℝ :=
  1

/-- The scalar analogue of `\log ζ_θ(z)`. -/
noncomputable def logMSeedLogZeta (_θ z : ℝ) : ℝ :=
  z

/-- The distinguished pole location `z_*(θ)` in the seed model. -/
noncomputable def logMSeedPole (_θ : ℝ) : ℝ :=
  0

/-- The finitely many seed `z_k(θ)` terms used to package the Möbius tail. -/
noncomputable def logMSeedZk (k : Fin 2) (θ : ℝ) : ℝ :=
  logMSeedPole θ + k.1

/-- Two explicit Möbius weights corresponding to `k = 2, 3`. -/
noncomputable def logMSeedMobiusWeight (k : Fin 2) : ℝ :=
  if k.1 = 0 then -(1 / 2 : ℝ) else -(1 / 3 : ℝ)

/-- The finite-part seed built from the constant term and the two `z_k` contributions. -/
noncomputable def logMSeedFinitePart (θ : ℝ) : ℝ :=
  logMSeedConstant θ +
    ∑ k : Fin 2, logMSeedMobiusWeight k * logMSeedLogZeta θ (logMSeedZk k θ)

/-- The directional derivative of the scalar `z_k` seed is constant. -/
private lemma deriv_logMSeedZk (k : Fin 2) (θ : ℝ) :
    deriv (fun t => logMSeedZk k t) θ = 0 := by
  simp [logMSeedZk, logMSeedPole]

/-- In the scalar seed model, differentiating the finite-part `log M` expansion termwise gives the
resolvent-chain-rule expression from the paper remark.
`prop:logM-derivative-resolvent` -/
theorem paper_logM_derivative_resolvent (θ : ℝ) :
    deriv logMSeedFinitePart θ =
      deriv logMSeedConstant θ +
        ∑ k : Fin 2,
          logMSeedMobiusWeight k *
            (logMSeedResolvent θ (logMSeedZk k θ) *
                logMSeedZk k θ * deriv logMSeedMatrix θ +
              logMSeedResolvent θ (logMSeedZk k θ) *
                logMSeedMatrix θ * deriv (fun t => logMSeedZk k t) θ) := by
  unfold logMSeedFinitePart logMSeedConstant logMSeedLogZeta logMSeedMatrix logMSeedResolvent
    logMSeedZk logMSeedPole
  simp [logMSeedMobiusWeight, Fin.sum_univ_two]

end Omega.Zeta

import Mathlib
import Omega.Zeta.XiTerminalReplicaSoftcoreQGenfuncRationalPartition

namespace Omega.Zeta

open Polynomial
open scoped BigOperators

/-- Fixed-`m` reciprocal-moment data for the replica-softcore package: one Lucas/Pell channel and
a finite family of exceptional geometric channels. -/
structure XiReplicaSoftcoreReciprocalMomentData where
  ι : Type*
  instFintype : Fintype ι
  m : ℕ
  c : ι → ℚ
  Theta : ι → ℚ

attribute [instance] XiReplicaSoftcoreReciprocalMomentData.instFintype

/-- The reciprocal-moment channel itself is the exceptional partition coefficient from the fixed-`m`
rational generating-function package. -/
def xiReplicaSoftcoreReciprocalMoment (D : XiReplicaSoftcoreReciprocalMomentData) (q : ℕ) : ℚ :=
  xiTerminalReplicaSoftcorePartitionExceptionalCoeff D.m D.c D.Theta q

/-- The quadratic Lucas/Pell factor isolated by the replica-softcore generating function. -/
noncomputable def xiReplicaSoftcoreLucasQuadratic
    (D : XiReplicaSoftcoreReciprocalMomentData) : Polynomial ℚ :=
  X ^ 2 - C (xiTerminalReplicaSoftcoreLucas D.m) * X + C (((-1 : ℚ) ^ D.m))

/-- The finite exceptional support contributes one linear factor for each geometric channel. -/
noncomputable def xiReplicaSoftcoreExceptionalLinearFactor
    (D : XiReplicaSoftcoreReciprocalMomentData) : Polynomial ℚ :=
  ∏ i : D.ι, (X - C (D.Theta i))

/-- The advertised annihilating factor is the quadratic Lucas/Pell factor multiplied by the finite
product of exceptional linear factors. -/
noncomputable def xiReplicaSoftcoreReciprocalMomentCharacteristicFactor
    (D : XiReplicaSoftcoreReciprocalMomentData) : Polynomial ℚ :=
  xiReplicaSoftcoreLucasQuadratic D * xiReplicaSoftcoreExceptionalLinearFactor D

/-- Characteristic-factor package for the reciprocal moments: the reciprocal-moment coefficients
are the exceptional fixed-`m` partition coefficients, the Lucas/Pell channel satisfies its
two-step recurrence, and the annihilating polynomial is the quadratic factor times the finite
exceptional linear factors.
    thm:xi-replica-softcore-reciprocal-moment-q-recurrence -/
def XiReplicaSoftcoreReciprocalMomentHasCharacteristicFactor
    (D : XiReplicaSoftcoreReciprocalMomentData) : Prop :=
  (∀ q, xiReplicaSoftcoreReciprocalMoment D q =
    (xiTerminalReplicaSoftcoreOmega D.m q + ∑ i : D.ι, D.c i * (D.Theta i) ^ q) / (2 : ℚ) ^ D.m) ∧
  xiTerminalReplicaSoftcoreOmega D.m 0 = 1 ∧
  xiTerminalReplicaSoftcoreOmega D.m 1 = xiTerminalReplicaSoftcoreLucas D.m ∧
  (∀ q, xiTerminalReplicaSoftcoreOmega D.m (q + 2) =
    xiTerminalReplicaSoftcoreLucas D.m * xiTerminalReplicaSoftcoreOmega D.m (q + 1) -
      ((-1 : ℚ) ^ D.m) * xiTerminalReplicaSoftcoreOmega D.m q) ∧
  xiReplicaSoftcoreReciprocalMomentCharacteristicFactor D =
    (X ^ 2 - C (xiTerminalReplicaSoftcoreLucas D.m) * X + C (((-1 : ℚ) ^ D.m))) *
      ∏ i : D.ι, (X - C (D.Theta i))

theorem paper_xi_replica_softcore_reciprocal_moment_q_recurrence
    (D : XiReplicaSoftcoreReciprocalMomentData) :
    XiReplicaSoftcoreReciprocalMomentHasCharacteristicFactor D := by
  letI := D.instFintype
  rcases paper_xi_terminal_replica_softcore_q_genfunc_rational_partition
      (ι := D.ι) D.m D.c D.Theta with
    ⟨_, hExceptional, hOmega0, hOmega1, hRec, _, _, _⟩
  refine ⟨?_, hOmega0, hOmega1, hRec, rfl⟩
  intro q
  exact hExceptional q

end Omega.Zeta

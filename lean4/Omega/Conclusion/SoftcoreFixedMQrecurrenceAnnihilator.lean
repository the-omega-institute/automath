import Mathlib
import Omega.Zeta.XiTerminalReplicaSoftcoreQGenfuncRationalPartition

namespace Omega.Conclusion

open Polynomial
open scoped BigOperators
open Omega.Zeta

/-- The fixed-`m` exceptional softcore word-trace sequence `S_m(q)`. -/
def softcoreFixedMWordTrace {ι : Type*} [Fintype ι]
    (m : ℕ) (c Theta : ι → ℚ) (q : ℕ) : ℚ :=
  xiTerminalReplicaSoftcorePartitionExceptionalCoeff m c Theta q

/-- The finite geometric correction in the fixed-`m` softcore decomposition. -/
def softcoreFixedMGeometricPart {ι : Type*} [Fintype ι]
    (c Theta : ι → ℚ) (q : ℕ) : ℚ :=
  ∑ i, c i * (Theta i) ^ q

/-- The quadratic Lucas/Pell factor annihilating the `Ω_m` channel. -/
noncomputable def softcoreFixedMLucasAnnihilator (m : ℕ) : Polynomial ℚ :=
  X ^ 2 - C (xiTerminalReplicaSoftcoreLucas m) * X + C (((-1 : ℚ) ^ m))

/-- The product of the linear geometric annihilators `E - τ`. -/
noncomputable def softcoreFixedMGeometricAnnihilator {ι : Type*} [Fintype ι]
    (Theta : ι → ℚ) : Polynomial ℚ :=
  ∏ i, (X - C (Theta i))

/-- The advertised fixed-`m` annihilator polynomial in the `q` direction. -/
noncomputable def softcoreFixedMQrecurrenceAnnihilator {ι : Type*} [Fintype ι]
    (m : ℕ) (Theta : ι → ℚ) : Polynomial ℚ :=
  softcoreFixedMLucasAnnihilator m * softcoreFixedMGeometricAnnihilator Theta

/-- Concrete package mirroring the paper argument: `S_m(q)` splits into the exceptional Lucas/Pell
channel plus finitely many geometric channels, and the annihilator is the product of the quadratic
Lucas factor with the linear geometric factors. -/
def SoftcoreFixedMQrecurrenceWitness {ι : Type*} [Fintype ι]
    (m : ℕ) (c Theta : ι → ℚ) : Prop :=
  (∀ q, softcoreFixedMWordTrace m c Theta q =
    (xiTerminalReplicaSoftcoreOmega m q + softcoreFixedMGeometricPart c Theta q) / (2 : ℚ) ^ m) ∧
  xiTerminalReplicaSoftcoreOmega m 0 = 1 ∧
  xiTerminalReplicaSoftcoreOmega m 1 = xiTerminalReplicaSoftcoreLucas m ∧
  (∀ q, xiTerminalReplicaSoftcoreOmega m (q + 2) =
    xiTerminalReplicaSoftcoreLucas m * xiTerminalReplicaSoftcoreOmega m (q + 1) -
      ((-1 : ℚ) ^ m) * xiTerminalReplicaSoftcoreOmega m q) ∧
  softcoreFixedMQrecurrenceAnnihilator m Theta =
    (X ^ 2 - C (xiTerminalReplicaSoftcoreLucas m) * X + C (((-1 : ℚ) ^ m))) *
      ∏ i, (X - C (Theta i))

/-- Paper label: `prop:conclusion-softcore-fixedm-qrecurrence-annihilator`. -/
theorem paper_conclusion_softcore_fixedm_qrecurrence_annihilator
    {ι : Type*} [Fintype ι] (m : ℕ) (c Theta : ι → ℚ) :
    SoftcoreFixedMQrecurrenceWitness m c Theta := by
  rcases paper_xi_terminal_replica_softcore_q_genfunc_rational_partition m c Theta with
    ⟨_, hExceptional, hOmega0, hOmega1, hRec, _, _, _⟩
  refine ⟨?_, hOmega0, hOmega1, hRec, rfl⟩
  intro q
  simpa [softcoreFixedMWordTrace, softcoreFixedMGeometricPart] using hExceptional q

end Omega.Conclusion

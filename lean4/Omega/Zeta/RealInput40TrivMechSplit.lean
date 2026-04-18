import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40NonzeroSpectrumTracePrimitive

namespace Omega.Zeta

open Omega.SyncKernelWeighted

/-- Concrete finite-part bookkeeping for the real-input-40 trivial/mechanism decomposition. -/
structure RealInput40TrivMechPackage where
  spectrum : RealInput40NonzeroSpectrumTracePrimitiveData
  carryConstant : ℤ

/-- Total finite-part constant after adding the carry-mechanism correction to the primitive trace
coming from the two nonzero determinant factors. -/
def totalFinitePartConstant (P : RealInput40TrivMechPackage) : ℤ :=
  realInput40PrimitiveTrace P.spectrum + P.carryConstant

/-- Contribution of the explicit trivial factor. -/
def trivialFactorContribution (P : RealInput40TrivMechPackage) : ℤ :=
  P.spectrum.α ^ P.spectrum.n

/-- Contribution of the nontrivial mechanism channel. -/
def mechanismContribution (P : RealInput40TrivMechPackage) : ℤ :=
  P.spectrum.β ^ P.spectrum.n + P.carryConstant

/-- Additive split of the finite-part constant into trivial and mechanism terms. -/
def splitIdentity (P : RealInput40TrivMechPackage) : Prop :=
  totalFinitePartConstant P = trivialFactorContribution P + mechanismContribution P

/-- Closed form for the trivial-factor piece. -/
def trivialClosedForm (P : RealInput40TrivMechPackage) : Prop :=
  trivialFactorContribution P = P.spectrum.α ^ P.spectrum.n

/-- The mechanism term is exactly the carry constant added to the second nonzero spectral
contribution. -/
def mechanismMatchesCarryConstant (P : RealInput40TrivMechPackage) : Prop :=
  mechanismContribution P - P.spectrum.β ^ P.spectrum.n = P.carryConstant

/-- `prop:real-input-40-triv-mech-split`. The determinant factorization gives the two nonzero
spectral terms, the primitive trace theorem rewrites the total trace in closed form, and the
carry constant isolates the mechanism contribution. -/
theorem paper_real_input_40_triv_mech_split (P : RealInput40TrivMechPackage) :
    splitIdentity P ∧ trivialClosedForm P ∧ mechanismMatchesCarryConstant P := by
  have hTrace :
      realInput40PrimitiveTrace P.spectrum = realInput40PrimitiveTraceClosedForm P.spectrum :=
    (paper_real_input_40_nonzero_spectrum_trace_primitive P.spectrum).2
  refine ⟨?_, by simp [trivialClosedForm, trivialFactorContribution], ?_⟩
  · dsimp [splitIdentity, totalFinitePartConstant, trivialFactorContribution,
      mechanismContribution]
    rw [hTrace]
    dsimp [realInput40PrimitiveTraceClosedForm]
    ring
  · dsimp [mechanismMatchesCarryConstant, mechanismContribution]
    ring

end Omega.Zeta

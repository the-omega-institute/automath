import Mathlib.Tactic
import Omega.POM.DelayMin
import Omega.POM.MomentKernelExists
import Omega.POM.MomentMinreal
import Omega.POM.MomentResonance
import Omega.POM.RenyiDimensionSpectrum
import Omega.SyncKernelWeighted.RealInput40NonzeroSpectrumTracePrimitive
import Omega.Zeta.RealInput40TrivMechSplit

namespace Omega.POM

open Omega.POM.RenyiDimensionSpectrum
open Omega.SyncKernelWeighted
open Omega.Zeta

/-- Concrete chapter-local data for the unified POM closure package. The delay witness is
global, while the moment/minreal, resonance, Rényi, and real-input-40 spectral packages are
recorded explicitly so the paper-facing theorem can assemble them into one closure statement. -/
structure pom_unified_closure_data where
  pom_unified_closure_momentOrder : ℕ
  pom_unified_closure_momentOrder_ge_two : 2 ≤ pom_unified_closure_momentOrder
  pom_unified_closure_minreal : MomentMinrealData
  pom_unified_closure_resonanceVisibleDim : ℕ
  pom_unified_closure_resonanceDefect : ℕ
  pom_unified_closure_resonanceStart : ℕ
  pom_unified_closure_resonanceMoments :
    ℕ →
      Fin (pom_unified_closure_resonanceVisibleDim + pom_unified_closure_resonanceDefect) → ℝ
  pom_unified_closure_resonanceChange :
    Matrix (Fin (pom_unified_closure_resonanceVisibleDim + pom_unified_closure_resonanceDefect))
      (Fin (pom_unified_closure_resonanceVisibleDim + pom_unified_closure_resonanceDefect)) ℝ
  pom_unified_closure_resonanceDetUnit :
    IsUnit pom_unified_closure_resonanceChange.det
  pom_unified_closure_resonanceTail :
    ∀ m ≥ pom_unified_closure_resonanceStart,
      ∀ j : Fin pom_unified_closure_resonanceDefect,
        (pom_unified_closure_resonanceChange.mulVec (pom_unified_closure_resonanceMoments m))
          (Fin.natAdd pom_unified_closure_resonanceVisibleDim j) = 0
  pom_unified_closure_resonanceDefect_pos :
    0 < pom_unified_closure_resonanceDefect
  pom_unified_closure_renyiQ : ℝ
  pom_unified_closure_renyiRate : ℝ
  pom_unified_closure_renyiSequence : ℕ → ℝ
  pom_unified_closure_renyiQ_ne_one : pom_unified_closure_renyiQ ≠ 1
  pom_unified_closure_logGoldenRatio_ne_zero : Real.log Real.goldenRatio ≠ 0
  pom_unified_closure_renyiLimit :
    Filter.Tendsto
      (pomRenyiEntropyRateSequence pom_unified_closure_renyiSequence)
      Filter.atTop
      (nhds pom_unified_closure_renyiRate)
  pom_unified_closure_spectrum : RealInput40NonzeroSpectrumTracePrimitiveData
  pom_unified_closure_trivMech : RealInput40TrivMechPackage
  pom_unified_closure_trivMech_uses_spectrum :
    pom_unified_closure_trivMech.spectrum = pom_unified_closure_spectrum

namespace pom_unified_closure_data

/-- The online kernel still witnesses the non-delay-2 time defect. -/
def onlineKernelAndTimeDefect (D : pom_unified_closure_data) : Prop :=
  let _ := D
  POMDelayMinStatement

/-- The finite-state moment kernel exists at the chosen order, and the minreal package identifies
the Hankel rank with the entropy-rate realization order. -/
def momentKernelAndEntropyRate (D : pom_unified_closure_data) : Prop :=
  (∃ K : MomentKernel D.pom_unified_closure_momentOrder,
      ∀ m ≥ K.m0,
        K.count m = momentCollisionCount D.pom_unified_closure_momentOrder m) ∧
    D.pom_unified_closure_minreal.hankelRank =
      D.pom_unified_closure_minreal.recurrenceOrder

/-- The closed realization dimension is invariant across the Hankel/minreal identification. -/
def closedDimensionInvariant (D : pom_unified_closure_data) : Prop :=
  D.pom_unified_closure_minreal.minimalRealizationDim =
    D.pom_unified_closure_minreal.recurrenceOrder

/-- The resonance package collapses the tail coordinates after an invertible change of basis. -/
def resonanceCollapseCriterion (D : pom_unified_closure_data) : Prop :=
  IsUnit D.pom_unified_closure_resonanceChange.det ∧
    ∃ reduced : ℕ → Fin D.pom_unified_closure_resonanceVisibleDim → ℝ,
      ∀ m ≥ D.pom_unified_closure_resonanceStart,
        (∀ i : Fin D.pom_unified_closure_resonanceVisibleDim,
            reduced m i =
              (D.pom_unified_closure_resonanceChange.mulVec
                  (D.pom_unified_closure_resonanceMoments m))
                (Fin.castAdd D.pom_unified_closure_resonanceDefect i)) ∧
          (∀ j : Fin D.pom_unified_closure_resonanceDefect,
              (D.pom_unified_closure_resonanceChange.mulVec
                  (D.pom_unified_closure_resonanceMoments m))
                (Fin.natAdd D.pom_unified_closure_resonanceVisibleDim j) = 0)

/-- The Rényi entropy-rate limit transfers to the geometric dimension spectrum. -/
def renyiDimensionSpectrum (D : pom_unified_closure_data) : Prop :=
  (∀ m : ℕ,
      pomRenyiDimensionApprox D.pom_unified_closure_renyiQ
          D.pom_unified_closure_renyiSequence m =
        pomRenyiEntropyRateSequence D.pom_unified_closure_renyiSequence m /
          ((D.pom_unified_closure_renyiQ - 1) * Real.log Real.goldenRatio)) ∧
    ((D.pom_unified_closure_renyiQ - 1) * Real.log Real.goldenRatio ≠ 0) ∧
    ∃ Dq : ℝ,
      Filter.Tendsto
        (pomRenyiDimensionApprox D.pom_unified_closure_renyiQ
          D.pom_unified_closure_renyiSequence)
        Filter.atTop
        (nhds Dq) ∧
        Dq =
          D.pom_unified_closure_renyiRate /
            ((D.pom_unified_closure_renyiQ - 1) * Real.log Real.goldenRatio)

/-- The real-input-40 nonzero spectrum controls both the primitive trace package and the
trivial/mechanism splitting package. -/
def mechanismKernelPeriodicPrimitive (D : pom_unified_closure_data) : Prop :=
  D.pom_unified_closure_trivMech.spectrum = D.pom_unified_closure_spectrum ∧
    D.pom_unified_closure_spectrum.nonzeroSpectrumAndTraceFormula ∧
    splitIdentity D.pom_unified_closure_trivMech ∧
    trivialClosedForm D.pom_unified_closure_trivMech ∧
    mechanismMatchesCarryConstant D.pom_unified_closure_trivMech

end pom_unified_closure_data

local notation "POMUnifiedClosureData" => pom_unified_closure_data

/-- Paper label: `thm:pom-unified-closure`. The already formalized delay, moment/minreal,
resonance, Rényi, and real-input-40 spectrum packages close into one audited conjunction. -/
theorem paper_pom_unified_closure (h : POMUnifiedClosureData) :
    h.onlineKernelAndTimeDefect /\ h.momentKernelAndEntropyRate /\
      h.closedDimensionInvariant /\ h.resonanceCollapseCriterion /\
      h.renyiDimensionSpectrum /\ h.mechanismKernelPeriodicPrimitive := by
  have hKernel :=
    paper_pom_moment_kernel_exists
      h.pom_unified_closure_momentOrder
      h.pom_unified_closure_momentOrder_ge_two
  have hMinreal := paper_pom_moment_minreal h.pom_unified_closure_minreal
  have hResonance :=
    paper_pom_moment_resonance
      h.pom_unified_closure_resonanceVisibleDim
      h.pom_unified_closure_resonanceDefect
      h.pom_unified_closure_resonanceStart
      h.pom_unified_closure_resonanceMoments
      h.pom_unified_closure_resonanceChange
      h.pom_unified_closure_resonanceDetUnit
      h.pom_unified_closure_resonanceTail
      h.pom_unified_closure_resonanceDefect_pos
  have hRenyi :=
    Omega.POM.RenyiDimensionSpectrum.paper_pom_renyi_dimension_spectrum
      h.pom_unified_closure_renyiQ
      h.pom_unified_closure_renyiRate
      h.pom_unified_closure_renyiSequence
      h.pom_unified_closure_renyiQ_ne_one
      h.pom_unified_closure_logGoldenRatio_ne_zero
      h.pom_unified_closure_renyiLimit
  have hSpectrum :=
    paper_real_input_40_nonzero_spectrum_trace_primitive h.pom_unified_closure_spectrum
  have hSplit := paper_real_input_40_triv_mech_split h.pom_unified_closure_trivMech
  refine ⟨paper_pom_delay_min, ⟨hKernel, hMinreal.1⟩, hMinreal.2, hResonance, hRenyi, ?_⟩
  rcases hSplit with ⟨hSplitIdentity, hTrivialClosedForm, hMechanismCarry⟩
  exact ⟨h.pom_unified_closure_trivMech_uses_spectrum, hSpectrum, hSplitIdentity,
    hTrivialClosedForm, hMechanismCarry⟩

end Omega.POM

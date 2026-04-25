import Mathlib.Data.Fintype.BigOperators
import Omega.Zeta.XiTimePart63cSchurCauchyMasterKernel

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete packet data for the trivial/alternating Schur sufficiency wrapper. The two packet
recovery clauses are recorded as explicit formulas, while the spectrum itself is a genuine finite
family of rational weights that can be fed into the existing Schur Cauchy kernel theorem. -/
structure XiTimePart63cTrivialAlternatingSchurCompleteSufficiencyData where
  α : Type
  instFintype : Fintype α
  spectrum : α → ℚ
  trivialPacket : ℚ → ℚ
  alternatingPacket : ℚ → ℚ
  recoveredCharpoly : ℚ → ℚ
  xi_time_part63c_trivial_alternating_schur_complete_sufficiency_trivial_recovery :
    ∀ z, recoveredCharpoly z * trivialPacket z = 1
  xi_time_part63c_trivial_alternating_schur_complete_sufficiency_alternating_recovery :
    ∀ z, recoveredCharpoly z = alternatingPacket (-z)

attribute [instance]
  XiTimePart63cTrivialAlternatingSchurCompleteSufficiencyData.instFintype

namespace XiTimePart63cTrivialAlternatingSchurCompleteSufficiencyData

/-- The trivial packet determines the recovered characteristic polynomial. -/
def trivialPacketRecoversSpectrum
    (D : XiTimePart63cTrivialAlternatingSchurCompleteSufficiencyData) : Prop :=
  ∀ z, D.recoveredCharpoly z * D.trivialPacket z = 1

/-- The alternating packet determines the same recovered characteristic polynomial after the
standard sign flip `z ↦ -z`. -/
def alternatingPacketRecoversSpectrum
    (D : XiTimePart63cTrivialAlternatingSchurCompleteSufficiencyData) : Prop :=
  ∀ z, D.recoveredCharpoly z = D.alternatingPacket (-z)

/-- Once the finite spectrum is known, all Schur statistics are recovered by the existing Cauchy
master-kernel identity. -/
def spectrumRecoversAllSchurData
    (D : XiTimePart63cTrivialAlternatingSchurCompleteSufficiencyData) : Prop :=
  ∀ {β : Type} [Fintype β] (y : β → ℚ),
    xiSchurTraceSeries D.spectrum y = xiSchurCauchyMasterKernel D.spectrum y ∧
      xiSchurCauchyMasterKernel D.spectrum y = ∏ j, xiHmKernel D.spectrum (y j)

end XiTimePart63cTrivialAlternatingSchurCompleteSufficiencyData

open XiTimePart63cTrivialAlternatingSchurCompleteSufficiencyData

/-- Paper label:
`thm:xi-time-part63c-trivial-alternating-schur-complete-sufficiency`. -/
theorem paper_xi_time_part63c_trivial_alternating_schur_complete_sufficiency
    (D : XiTimePart63cTrivialAlternatingSchurCompleteSufficiencyData) :
    D.trivialPacketRecoversSpectrum ∧ D.alternatingPacketRecoversSpectrum ∧
      D.spectrumRecoversAllSchurData := by
  refine ⟨D.xi_time_part63c_trivial_alternating_schur_complete_sufficiency_trivial_recovery,
    D.xi_time_part63c_trivial_alternating_schur_complete_sufficiency_alternating_recovery, ?_⟩
  intro β _ y
  simpa using (paper_xi_time_part63c_schur_cauchy_master_kernel (d := D.spectrum) (y := y))

end Omega.Zeta

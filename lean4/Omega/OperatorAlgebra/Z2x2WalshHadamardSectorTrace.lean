import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Finite scalar model for the two involutions `ε_scan`, `ε_rev`, an operator `T`, and the
associated mixed trace moments. Since the data live in `ℝ`, the commutation assumptions are
automatic and the Walsh-Hadamard inversion reduces to an exact algebraic identity. -/
structure WalshHadamardSectorTraceData where
  scanInvolution : ℝ
  revInvolution : ℝ
  T : ℝ

/-- Signs `±1` encoded by booleans. -/
def walshSign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The mixed trace moment `m_{s,t}(T)`. -/
def WalshHadamardSectorTraceData.mixedMoment
    (D : WalshHadamardSectorTraceData) (s t : Bool) : ℝ :=
  (if s then D.scanInvolution else 1) * (if t then D.revInvolution else 1) * D.T

/-- The sector idempotent `e_{α,β} = (1/4) (1 + α ε_scan) (1 + β ε_rev)`. -/
noncomputable def WalshHadamardSectorTraceData.sectorProjector
    (D : WalshHadamardSectorTraceData) (α β : Bool) : ℝ :=
  ((1 : ℝ) / 4) * (1 + walshSign α * D.scanInvolution) * (1 + walshSign β * D.revInvolution)

/-- The sector trace `τ(e_{α,β} T)`. -/
noncomputable def WalshHadamardSectorTraceData.sectorTrace
    (D : WalshHadamardSectorTraceData) (α β : Bool) : ℝ :=
  D.sectorProjector α β * D.T

/-- The Walsh-Hadamard inversion formula for the four mixed trace moments. -/
def WalshHadamardSectorTraceData.traceInversion (D : WalshHadamardSectorTraceData) : Prop :=
  ∀ α β,
    D.sectorTrace α β =
      ((1 : ℝ) / 4) *
        (D.mixedMoment false false
          + walshSign α * D.mixedMoment true false
          + walshSign β * D.mixedMoment false true
          + walshSign α * walshSign β * D.mixedMoment true true)

/-- Expanding the two commuting central involutions gives the four mixed moments with the
Walsh-Hadamard coefficients.
    prop:op-algebra-z2x2-walsh-hadamard-sector-trace -/
theorem paper_op_algebra_z2x2_walsh_hadamard_sector_trace
    (D : WalshHadamardSectorTraceData) : D.traceInversion := by
  intro α β
  cases α <;> cases β <;>
    simp [WalshHadamardSectorTraceData.sectorTrace,
      WalshHadamardSectorTraceData.sectorProjector, WalshHadamardSectorTraceData.mixedMoment,
      walshSign] <;>
    ring

end Omega.OperatorAlgebra

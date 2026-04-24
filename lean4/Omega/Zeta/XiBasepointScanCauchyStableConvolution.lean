import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace Omega.Zeta

/-- A symbolic weighted shifted Cauchy kernel. The `location` parameter is the shift/scale label
that adds under convolution, while the weight multiplies. -/
structure CauchyAtom where
  location : ℝ
  weight : ℂ

/-- Symbolic convolution of two Cauchy atoms, modeling `P_a * P_b = P_(a+b)`. -/
def cauchyAtomConvolution (A B : CauchyAtom) : CauchyAtom :=
  { location := A.location + B.location, weight := A.weight * B.weight }

/-- The identity atom for the symbolic convolution. -/
def cauchyUnitAtom : CauchyAtom :=
  { location := 0, weight := 1 }

/-- Constructor for a weighted shifted Cauchy kernel. -/
def weightedShiftedCauchyKernel (a : ℝ) (w : ℂ) : CauchyAtom :=
  { location := a, weight := w }

@[simp] theorem cauchy_unit_left (A : CauchyAtom) :
    cauchyAtomConvolution cauchyUnitAtom A = A := by
  cases A
  simp [cauchyAtomConvolution, cauchyUnitAtom]

@[simp] theorem cauchy_unit_right (A : CauchyAtom) :
    cauchyAtomConvolution A cauchyUnitAtom = A := by
  cases A
  simp [cauchyAtomConvolution, cauchyUnitAtom]

/-- Binary Cauchy stability: the convolution parameter adds and the weights multiply. -/
@[simp] theorem weighted_shifted_cauchy_kernel_convolution (a b : ℝ) (w z : ℂ) :
    cauchyAtomConvolution (weightedShiftedCauchyKernel a w) (weightedShiftedCauchyKernel b z) =
      weightedShiftedCauchyKernel (a + b) (w * z) := by
  rfl

/-- Pairwise convolution of two finite Cauchy mixtures. -/
def mixConvolution : List CauchyAtom → List CauchyAtom → List CauchyAtom
  | [], _ => []
  | A :: L, M => M.map (fun B => cauchyAtomConvolution A B) ++ mixConvolution L M

@[simp] theorem length_mixConvolution (L M : List CauchyAtom) :
    (mixConvolution L M).length = L.length * M.length := by
  induction L with
  | nil =>
      simp [mixConvolution]
  | cons A L ih =>
      simp [mixConvolution, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem mixConvolution_singleton_unit (L : List CauchyAtom) :
    mixConvolution [cauchyUnitAtom] L = L := by
  simp [mixConvolution]

/-- Concrete basepoint-scan data for a finite weighted Cauchy mixture. -/
structure BasepointScanDatum where
  kappa : Nat
  location : Fin kappa → ℝ
  weight : Fin kappa → ℂ

namespace BasepointScanDatum

/-- The base scan profile `H` as a finite weighted sum of shifted Cauchy atoms. -/
def scanMix (D : BasepointScanDatum) : List CauchyAtom :=
  List.ofFn fun i => weightedShiftedCauchyKernel (D.location i) (D.weight i)

/-- Iterated symbolic convolution of the base scan profile. -/
def nFoldMix (D : BasepointScanDatum) : Nat → List CauchyAtom
  | 0 => [cauchyUnitAtom]
  | n + 1 => mixConvolution (D.nFoldMix n) D.scanMix

/-- The explicit pairwise formula for `H * H`. -/
def selfConvolutionTerms (D : BasepointScanDatum) : List CauchyAtom :=
  mixConvolution D.scanMix D.scanMix

/-- The scan profile is closed under self-convolution with the pairwise sum-set formula. -/
def selfConvolutionClosedForm (D : BasepointScanDatum) : Prop :=
  D.nFoldMix 2 = D.selfConvolutionTerms

/-- Every iterated convolution remains a finite Cauchy mixture, with exactly `κ^n` terms before
any coefficient aggregation. -/
def nFoldConvolutionIsFiniteCauchyMix (D : BasepointScanDatum) (n : Nat) : Prop :=
  ∃ terms : List CauchyAtom, D.nFoldMix n = terms ∧ terms.length = D.kappa ^ n

@[simp] theorem length_scanMix (D : BasepointScanDatum) :
    D.scanMix.length = D.kappa := by
  simp [scanMix]

theorem nFoldMix_length (D : BasepointScanDatum) : ∀ n : Nat, (D.nFoldMix n).length = D.kappa ^ n
  | 0 => by simp [nFoldMix]
  | n + 1 => by
      simp [nFoldMix, nFoldMix_length D n, Nat.pow_succ, Nat.mul_comm]

end BasepointScanDatum

open BasepointScanDatum

/-- `prop:xi-basepoint-scan-cauchy-stable-convolution` -/
theorem paper_xi_basepoint_scan_cauchy_stable_convolution (D : BasepointScanDatum) :
    D.selfConvolutionClosedForm ∧
      ∀ n : Nat, 2 ≤ n → D.nFoldConvolutionIsFiniteCauchyMix n := by
  refine ⟨?_, ?_⟩
  · simp [BasepointScanDatum.selfConvolutionClosedForm, BasepointScanDatum.selfConvolutionTerms,
      BasepointScanDatum.nFoldMix]
  · intro n _hn
    exact ⟨D.nFoldMix n, rfl, D.nFoldMix_length n⟩

end Omega.Zeta

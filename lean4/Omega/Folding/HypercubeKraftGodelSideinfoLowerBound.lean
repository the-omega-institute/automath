import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete finite package for the Kraft/Jensen side-information lower bound. The package keeps
the averaged fiber-log term, the gauge-volume correction, and the area correction as explicit real
quantities so that the displayed inequalities follow by monotonicity of division by `log M`. -/
structure HypercubeKraftGodelSideinfoPackage where
  n : ℕ
  alphabetSize : ℝ
  averageSideinfo : ℝ
  fiberLogAverage : ℝ
  gaugeDensity : ℝ
  imageCardinality : ℝ
  area : ℝ
  logAlphabet_pos : 0 < Real.log alphabetSize
  kraftBound :
    fiberLogAverage / Real.log alphabetSize ≤ averageSideinfo
  gaugeFiberLower :
    gaugeDensity + 1 - imageCardinality / (2 : ℝ) ^ n ≤ fiberLogAverage
  gaugeAreaLower :
    (n : ℝ) * Real.log 2 - Real.log 2 * area / (2 : ℝ) ^ (n - 1) ≤
      gaugeDensity + 1 - imageCardinality / (2 : ℝ) ^ n

namespace HypercubeKraftGodelSideinfoPackage

/-- The averaged fiberwise Kraft/Jensen estimate. -/
def kraftJensenLowerBound (P : HypercubeKraftGodelSideinfoPackage) : Prop :=
  P.averageSideinfo ≥ P.fiberLogAverage / Real.log P.alphabetSize

/-- Combining the fiber-log lower bound with the gauge/area lower bound gives the global bound. -/
def gaugeAreaLowerBound (P : HypercubeKraftGodelSideinfoPackage) : Prop :=
  P.averageSideinfo ≥
    (((P.n : ℝ) * Real.log 2 - Real.log 2 * P.area / (2 : ℝ) ^ (P.n - 1)) /
      Real.log P.alphabetSize)

/-- Specializing the alphabet size to `2` recovers the binary lower bound. -/
def binaryAlphabetSpecialization (P : HypercubeKraftGodelSideinfoPackage) : Prop :=
  P.alphabetSize = 2 →
    P.averageSideinfo ≥ (P.n : ℝ) - P.area / (2 : ℝ) ^ (P.n - 1)

end HypercubeKraftGodelSideinfoPackage

open HypercubeKraftGodelSideinfoPackage

/-- Fiberwise Kraft/Jensen, summed over the coarse-graining fibers and combined with the
gauge-volume area bound, yields the global side-information lower bound and its binary
specialization.
    thm:hypercube-kraft-godel-sideinfo-lower-bound -/
theorem paper_hypercube_kraft_godel_sideinfo_lower_bound
    (P : HypercubeKraftGodelSideinfoPackage) :
    HypercubeKraftGodelSideinfoPackage.kraftJensenLowerBound P ∧
      HypercubeKraftGodelSideinfoPackage.gaugeAreaLowerBound P ∧
      HypercubeKraftGodelSideinfoPackage.binaryAlphabetSpecialization P := by
  have hnum :
      (P.n : ℝ) * Real.log 2 - Real.log 2 * P.area / (2 : ℝ) ^ (P.n - 1) ≤
        P.fiberLogAverage := by
    exact le_trans P.gaugeAreaLower P.gaugeFiberLower
  have hdiv :
      (((P.n : ℝ) * Real.log 2 - Real.log 2 * P.area / (2 : ℝ) ^ (P.n - 1)) /
          Real.log P.alphabetSize) ≤
        P.fiberLogAverage / Real.log P.alphabetSize := by
    exact div_le_div_of_nonneg_right hnum P.logAlphabet_pos.le
  have hglobal : HypercubeKraftGodelSideinfoPackage.gaugeAreaLowerBound P := by
    exact le_trans hdiv P.kraftBound
  refine ⟨P.kraftBound, hglobal, ?_⟩
  · intro hbin
    have hmain :
        (((P.n : ℝ) * Real.log 2 - Real.log 2 * P.area / (2 : ℝ) ^ (P.n - 1)) /
            Real.log P.alphabetSize) ≤
          P.averageSideinfo := by
      exact hglobal
    rw [ge_iff_le]
    rw [hbin] at hmain
    have hlog2 : Real.log 2 ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num)
    have hrewrite :
        (((P.n : ℝ) * Real.log 2 - Real.log 2 * P.area / (2 : ℝ) ^ (P.n - 1)) / Real.log 2) =
          (P.n : ℝ) - P.area / (2 : ℝ) ^ (P.n - 1) := by
      field_simp [hlog2]
    rw [hrewrite] at hmain
    exact hmain

end Omega.Folding

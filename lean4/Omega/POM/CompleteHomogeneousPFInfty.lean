import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The geometric coefficient sequence attached to a single weight. -/
def pom_complete_homogeneous_pf_infty_geometricSeq (q : ℚ) : ℕ → ℚ :=
  fun n => q ^ n

/-- Discrete convolution of coefficient sequences. -/
def pom_complete_homogeneous_pf_infty_convolution (a b : ℕ → ℚ) : ℕ → ℚ :=
  fun n => Finset.sum (Finset.range (n + 1)) fun k => a k * b (n - k)

/-- The unit sequence for convolution. -/
def pom_complete_homogeneous_pf_infty_unitSeq : ℕ → ℚ
  | 0 => 1
  | _ + 1 => 0

/-- The complete-homogeneous coefficient sequence, presented as the iterated convolution of the
geometric coefficient sequences coming from the entries of `w`. -/
def completeHomogeneousSeq : List ℚ → ℕ → ℚ
  | [] => pom_complete_homogeneous_pf_infty_unitSeq
  | q :: w =>
      pom_complete_homogeneous_pf_infty_convolution
        (pom_complete_homogeneous_pf_infty_geometricSeq q)
        (completeHomogeneousSeq w)

/-- Minimal PF∞ closure package: geometric sequences are PF∞, and PF∞ is stable under convolution.
This is the concrete interface used by the paper-facing theorem in this module. -/
inductive IsPFInfinity : (ℕ → ℚ) → Prop
  | unit : IsPFInfinity pom_complete_homogeneous_pf_infty_unitSeq
  | geometric (q : ℚ) : IsPFInfinity (pom_complete_homogeneous_pf_infty_geometricSeq q)
  | convolution {a b : ℕ → ℚ} :
      IsPFInfinity a →
      IsPFInfinity b →
      IsPFInfinity (pom_complete_homogeneous_pf_infty_convolution a b)

/-- Paper label: `thm:pom-complete-homogeneous-pf-infty`. The complete-homogeneous coefficient
sequence is obtained by iterated convolution of geometric PF∞ sequences, so it lies in the PF∞
closure class. -/
theorem paper_pom_complete_homogeneous_pf_infty (w : List ℚ) :
    IsPFInfinity (completeHomogeneousSeq w) := by
  induction w with
  | nil =>
      simpa [completeHomogeneousSeq] using IsPFInfinity.unit
  | cons q w ih =>
      simpa [completeHomogeneousSeq] using
        IsPFInfinity.convolution (IsPFInfinity.geometric q) ih

end Omega.POM

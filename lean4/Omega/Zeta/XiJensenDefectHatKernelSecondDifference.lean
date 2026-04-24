import Mathlib
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite atomic model for the Jensen-defect hat-kernel identity. -/
structure XiJensenHatKernelData where
  ι : Type*
  instFintype : Fintype ι
  instDecidableEq : DecidableEq ι
  x : ℝ
  h : ℝ
  location : ι → ℝ
  multiplicity : ι → ℕ
  h_nonneg : 0 ≤ h
  hmult_pos : ∀ i, 0 < multiplicity i

attribute [instance] XiJensenHatKernelData.instFintype
attribute [instance] XiJensenHatKernelData.instDecidableEq

namespace XiJensenHatKernelData

def positivePart (u : ℝ) : ℝ :=
  max u 0

/-- Finite Jensen profile `J_F(x) = Σ_k m_k (x - t_k)_+`. -/
def jensenProfile (D : XiJensenHatKernelData) (y : ℝ) : ℝ :=
  ∑ i, (D.multiplicity i : ℝ) * positivePart (y - D.location i)

/-- The centered second difference at the fixed scale `h`. -/
def centeredSecondDifference (D : XiJensenHatKernelData) : ℝ :=
  ∑ i,
    (D.multiplicity i : ℝ) *
      (positivePart (D.x + D.h - D.location i) -
        2 * positivePart (D.x - D.location i) +
        positivePart (D.x - D.h - D.location i))

/-- The hat kernel `(h - |x - t|)_+`. -/
def hatKernel (D : XiJensenHatKernelData) (t : ℝ) : ℝ :=
  positivePart (D.h - |D.x - t|)

def secondDifferenceHatKernel (D : XiJensenHatKernelData) : Prop :=
  D.centeredSecondDifference = ∑ i, (D.multiplicity i : ℝ) * D.hatKernel (D.location i)

def zeroWindow (D : XiJensenHatKernelData) : Prop :=
  D.centeredSecondDifference = 0

def windowMassZero (D : XiJensenHatKernelData) : Prop :=
  ∀ i, D.h ≤ |D.x - D.location i|

private lemma positivePart_secondDifference_eq_hatKernel
    (x h t : ℝ) (hh : 0 ≤ h) :
    max (x + h - t) 0 - 2 * max (x - t) 0 + max (x - h - t) 0 = max (h - |x - t|) 0 := by
  by_cases hleft : x ≤ t - h
  · have hxph : x + h ≤ t := by linarith
    have hxm : x ≤ t := by linarith
    have hxmh : x - h ≤ t := by linarith
    have hxph' : x + h - t ≤ 0 := by linarith
    have hxm' : x - t ≤ 0 := by linarith
    have hxmh' : x - h - t ≤ 0 := by linarith
    have habs : |x - t| = t - x := by
      simpa using (abs_of_nonpos hxm' : |x - t| = -(x - t))
    have hrhs : h - (t - x) ≤ 0 := by linarith
    have h1 : max (x + h - t) 0 = 0 := max_eq_right hxph'
    have h2 : max (x - t) 0 = 0 := max_eq_right hxm'
    have h3 : max (x - h - t) 0 = 0 := max_eq_right hxmh'
    have h4 : max (h - (t - x)) 0 = 0 := max_eq_right hrhs
    rw [habs, h1, h2, h3, h4]
    ring
  · by_cases hmidLeft : x ≤ t
    · have hleft' : t - h ≤ x := by linarith
      have hxph : 0 ≤ x + h - t := by linarith
      have hxm : x - t ≤ 0 := by linarith
      have hxmh : x - h - t ≤ 0 := by linarith
      have habs : |x - t| = t - x := by
        simpa using (abs_of_nonpos hxm : |x - t| = -(x - t))
      have hrhs : 0 ≤ h - (t - x) := by linarith
      have h1 : max (x + h - t) 0 = x + h - t := max_eq_left hxph
      have h2 : max (x - t) 0 = 0 := max_eq_right hxm
      have h3 : max (x - h - t) 0 = 0 := max_eq_right hxmh
      have h4 : max (h - (t - x)) 0 = h - (t - x) := max_eq_left hrhs
      rw [habs, h1, h2, h3, h4]
      ring
    · by_cases hmidRight : x ≤ t + h
      · have ht : t ≤ x := by linarith
        have hxph : 0 ≤ x + h - t := by linarith
        have hxm : 0 ≤ x - t := by linarith
        have hxmh : x - h - t ≤ 0 := by linarith
        have habs : |x - t| = x - t := by
          rw [abs_of_nonneg]
          linarith
        have hrhs : 0 ≤ h - (x - t) := by linarith
        rw [habs]
        rw [max_eq_left hxph, max_eq_left hxm, max_eq_right hxmh, max_eq_left hrhs]
        ring
      · have hright : t + h ≤ x := by linarith
        have ht : t ≤ x := by linarith
        have hxph : 0 ≤ x + h - t := by linarith
        have hxm : 0 ≤ x - t := by linarith
        have hxmh : 0 ≤ x - h - t := by linarith
        have habs : |x - t| = x - t := by
          rw [abs_of_nonneg]
          linarith
        have hrhs : h - (x - t) ≤ 0 := by linarith
        rw [habs]
        rw [max_eq_left hxph, max_eq_left hxm, max_eq_left hxmh, max_eq_right hrhs]
        ring

lemma centeredSecondDifference_eq_hatKernel (D : XiJensenHatKernelData) :
    D.centeredSecondDifference = ∑ i, (D.multiplicity i : ℝ) * D.hatKernel (D.location i) := by
  unfold centeredSecondDifference hatKernel
  refine Finset.sum_congr rfl ?_
  intro i hi
  congr 1
  simpa [positivePart] using
    positivePart_secondDifference_eq_hatKernel D.x D.h (D.location i) D.h_nonneg

lemma hatKernel_nonneg (D : XiJensenHatKernelData) (t : ℝ) : 0 ≤ D.hatKernel t := by
  unfold hatKernel positivePart
  exact le_max_right _ _

lemma hatKernel_eq_zero_iff (D : XiJensenHatKernelData) (t : ℝ) :
    D.hatKernel t = 0 ↔ D.h ≤ |D.x - t| := by
  unfold hatKernel positivePart
  constructor
  · intro hzero
    by_contra hlt
    have hlt' : |D.x - t| < D.h := lt_of_not_ge hlt
    have hpos : 0 < D.h - |D.x - t| := sub_pos.mpr hlt'
    have hmax : max (D.h - |D.x - t|) 0 = D.h - |D.x - t| := max_eq_left hpos.le
    linarith
  · intro hle
    have hnonpos : D.h - |D.x - t| ≤ 0 := sub_nonpos.mpr hle
    simp [hnonpos]

lemma zeroWindow_iff_hatKernel_vanishes (D : XiJensenHatKernelData) :
    D.zeroWindow ↔ ∀ i, D.hatKernel (D.location i) = 0 := by
  have hrepr := D.centeredSecondDifference_eq_hatKernel
  have hnonneg :
      ∀ i, 0 ≤ (D.multiplicity i : ℝ) * D.hatKernel (D.location i) := by
    intro i
    exact mul_nonneg (show 0 ≤ (D.multiplicity i : ℝ) from by positivity)
      (D.hatKernel_nonneg _)
  have hsum :
      D.zeroWindow ↔
        (fun i => (D.multiplicity i : ℝ) * D.hatKernel (D.location i)) = 0 := by
    rw [zeroWindow, hrepr]
    simpa using
      (Fintype.sum_eq_zero_iff_of_nonneg
        (f := fun i => (D.multiplicity i : ℝ) * D.hatKernel (D.location i)) hnonneg)
  refine hsum.trans ?_
  constructor
  · intro h i
    have hi := congrFun h i
    have hm : ((D.multiplicity i : ℝ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (D.hmult_pos i)
    exact (mul_eq_zero.mp hi).resolve_left hm
  · intro h
    funext i
    simp [h i]

lemma zeroWindow_iff_windowMassZero (D : XiJensenHatKernelData) :
    D.zeroWindow ↔ D.windowMassZero := by
  refine D.zeroWindow_iff_hatKernel_vanishes.trans ?_
  simp [windowMassZero, D.hatKernel_eq_zero_iff]

end XiJensenHatKernelData

open XiJensenHatKernelData

/-- Paper label: `thm:xi-jensen-defect-hat-kernel-second-difference`. -/
theorem paper_xi_jensen_defect_hat_kernel_second_difference (D : XiJensenHatKernelData) :
    D.secondDifferenceHatKernel ∧ (D.zeroWindow ↔ D.windowMassZero) := by
  refine ⟨D.centeredSecondDifference_eq_hatKernel, D.zeroWindow_iff_windowMassZero⟩

end Omega.Zeta

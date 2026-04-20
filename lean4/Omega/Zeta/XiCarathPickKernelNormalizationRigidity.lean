import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Scalar Carath--Pick kernel attached to a complex-valued function. -/
noncomputable def carathPickKernel (F : ℂ → ℂ) (w z : ℂ) : ℂ :=
  (F w + star (F z)) / (1 - w * star z)

/-- Equality of Carath--Pick kernels forces the functions to differ by a unique imaginary
constant.
    thm:xi-carath-pick-kernel-normalization-rigidity -/
theorem paper_xi_carath_pick_kernel_normalization_rigidity
    (F₁ F₂ : ℂ → ℂ)
    (hK : ∀ w z : ℂ, carathPickKernel F₁ w z = carathPickKernel F₂ w z) :
    ∃! β : ℝ, ∀ w : ℂ, F₁ w = F₂ w + Complex.I * (β : ℂ) := by
  let d : ℂ := F₁ 0 - F₂ 0
  have h00 : F₁ 0 + star (F₁ 0) = F₂ 0 + star (F₂ 0) := by
    simpa [carathPickKernel] using hK 0 0
  have hd_conj : star (F₂ 0) - star (F₁ 0) = d := by
    calc
      star (F₂ 0) - star (F₁ 0) = (F₂ 0 + star (F₂ 0)) - (F₂ 0 + star (F₁ 0)) := by ring
      _ = (F₁ 0 + star (F₁ 0)) - (F₂ 0 + star (F₁ 0)) := by rw [h00]
      _ = F₁ 0 - F₂ 0 := by ring
      _ = d := rfl
  have hconst : ∀ w : ℂ, F₁ w - F₂ w = d := by
    intro w
    have hw0 : F₁ w + star (F₁ 0) = F₂ w + star (F₂ 0) := by
      simpa [carathPickKernel] using hK w 0
    calc
      F₁ w - F₂ w = (F₁ w + star (F₁ 0)) - (F₂ w + star (F₁ 0)) := by ring
      _ = (F₂ w + star (F₂ 0)) - (F₂ w + star (F₁ 0)) := by rw [hw0]
      _ = star (F₂ 0) - star (F₁ 0) := by ring
      _ = d := hd_conj
  have hd_skew : d + star d = 0 := by
    unfold d
    calc
      (F₁ 0 - F₂ 0) + star (F₁ 0 - F₂ 0) = (F₁ 0 + star (F₁ 0)) - (F₂ 0 + star (F₂ 0)) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = 0 := by rw [h00]; ring
  have hd_re : d.re = 0 := by
    have hRe := congrArg Complex.re hd_skew
    simpa [two_mul] using hRe
  have hd_imaginary : d = Complex.I * (d.im : ℂ) := by
    apply Complex.ext
    · simp [hd_re]
    · simp
  let β : ℝ := d.im
  have hd_beta : d = Complex.I * (β : ℂ) := by
    simpa [β] using hd_imaginary
  have hshift : ∀ w : ℂ, F₁ w = F₂ w + Complex.I * (β : ℂ) := by
    intro w
    have hw : F₁ w = d + F₂ w := (sub_eq_iff_eq_add).mp (hconst w)
    calc
      F₁ w = d + F₂ w := hw
      _ = Complex.I * (β : ℂ) + F₂ w := by rw [hd_beta]
      _ = F₂ w + Complex.I * (β : ℂ) := by ring
  refine ⟨β, hshift, ?_⟩
  · intro γ hγ
    have hEq : F₂ 0 + Complex.I * (β : ℂ) = F₂ 0 + Complex.I * (γ : ℂ) := by
      rw [← hshift 0, hγ 0]
    have hImaginary : Complex.I * (β : ℂ) = Complex.I * (γ : ℂ) := add_left_cancel hEq
    have him := congrArg Complex.im hImaginary
    simpa [β] using him.symm

end Omega.Zeta

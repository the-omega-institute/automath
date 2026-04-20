import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- A nontrivial Fourier coefficient written in real and imaginary parts. -/
def arity335PairedCoefficient (a b : ℝ) : ℂ :=
  a + b * Complex.I

/-- Self-dual conjugation means that the coefficient is fixed by complex conjugation. -/
def arity335SelfDualConjugation (a b : ℝ) : Prop :=
  star (arity335PairedCoefficient a b) = arity335PairedCoefficient a b

/-- The real inverse DFT after pairing the `±1` and `±2` characters on the third-axis cyclic
group. -/
def arity335InverseDFT (a0 a1 b1 a2 b2 : ℝ) (θ : ℝ) : ℝ :=
  a0 + 2 * (a1 * Real.cos θ - b1 * Real.sin θ) +
    2 * (a2 * Real.cos (2 * θ) - b2 * Real.sin (2 * θ))

/-- The cosine-only expansion obtained once self-duality kills the sine modes. -/
def arity335CosineOnlyExpansion (a0 a1 a2 : ℝ) (θ : ℝ) : ℝ :=
  a0 + 2 * a1 * Real.cos θ + 2 * a2 * Real.cos (2 * θ)

/-- Concrete cosine-only statement for the `(3,3,5)` third-axis Fourier expansion. -/
def arity335CosineOnlyStatement : Prop :=
  ∀ a0 a1 b1 a2 b2 : ℝ,
    arity335SelfDualConjugation a1 b1 →
      arity335SelfDualConjugation a2 b2 →
      (∀ θ, arity335InverseDFT a0 a1 b1 a2 b2 θ = arity335CosineOnlyExpansion a0 a1 a2 θ) ∧
      (∀ θ, arity335InverseDFT a0 a1 b1 a2 b2 (-θ) = arity335InverseDFT a0 a1 b1 a2 b2 θ)

lemma arity335SelfDualConjugation_im_zero {a b : ℝ} (h : arity335SelfDualConjugation a b) : b = 0 := by
  unfold arity335SelfDualConjugation arity335PairedCoefficient at h
  have him := congrArg Complex.im h
  simp at him
  linarith

/-- Paper label: `cor:arity-335-cosine-only`. -/
def paper_arity_335_cosine_only : Prop :=
  arity335CosineOnlyStatement

set_option maxHeartbeats 400000 in
theorem paper_arity_335_cosine_only_verified : paper_arity_335_cosine_only := by
  unfold paper_arity_335_cosine_only arity335CosineOnlyStatement
  intro a0 a1 b1 a2 b2 h1 h2
  have hb1 : b1 = 0 := arity335SelfDualConjugation_im_zero h1
  have hb2 : b2 = 0 := arity335SelfDualConjugation_im_zero h2
  refine ⟨?_, ?_⟩
  · intro θ
    simp [arity335InverseDFT, arity335CosineOnlyExpansion, hb1, hb2]
    ring
  · intro θ
    simp [arity335InverseDFT, hb1, hb2, Real.cos_neg, Real.sin_neg]

end

end Omega.Zeta

import Mathlib.Tactic
import Omega.POM.DiagonalRateSturmCauchyEigenbasis

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The weighted norm of the `i`-th Sturm--Cauchy eigenfunction. -/
def pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer
    (D : DiagonalRateSturmCauchyEigenbasisData) (i : D.Mode) : ℝ :=
  diagonalRateSturmCauchyWeightedInner D
    (diagonalRateSturmCauchyEigenfunction D i)
    (diagonalRateSturmCauchyEigenfunction D i)

/-- The rank-one spectral-projector kernel attached to the `i`-th mode. -/
def pom_diagonal_rate_spectral_projector_residue_and_transition_projectorKernel
    (D : DiagonalRateSturmCauchyEigenbasisData) (i : D.Mode) (x y : D.State) : ℝ :=
  diagonalRateSturmCauchyStationaryWeight D y *
    diagonalRateSturmCauchyEigenfunction D i x *
    diagonalRateSturmCauchyEigenfunction D i y *
    (pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i)⁻¹

/-- The projector applied to a test function. -/
def pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply
    (D : DiagonalRateSturmCauchyEigenbasisData) (i : D.Mode) (f : D.State → ℝ) (x : D.State) : ℝ :=
  ∑ y, pom_diagonal_rate_spectral_projector_residue_and_transition_projectorKernel D i x y * f y

/-- The exact spectral transition kernel at step `m`. -/
def pom_diagonal_rate_spectral_projector_residue_and_transition_transitionKernel
    (D : DiagonalRateSturmCauchyEigenbasisData) (m : ℕ) (x y : D.State) : ℝ :=
  ∑ i, (D.z i) ^ m *
    pom_diagonal_rate_spectral_projector_residue_and_transition_projectorKernel D i x y

/-- The simple-pole residue attached to the `i`-th resolvent pole. -/
def pom_diagonal_rate_spectral_projector_residue_and_transition_resolventResidue
    (D : DiagonalRateSturmCauchyEigenbasisData) (i : D.Mode) (x y : D.State) : ℝ :=
  -pom_diagonal_rate_spectral_projector_residue_and_transition_projectorKernel D i x y *
    (D.z i)⁻¹

lemma pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply_eq
    (D : DiagonalRateSturmCauchyEigenbasisData) (i : D.Mode) (f : D.State → ℝ) (x : D.State) :
    pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i f x =
      diagonalRateSturmCauchyEigenfunction D i x *
        (pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i)⁻¹ *
        diagonalRateSturmCauchyWeightedInner D (diagonalRateSturmCauchyEigenfunction D i) f := by
  unfold pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply
    pom_diagonal_rate_spectral_projector_residue_and_transition_projectorKernel
    pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer
    diagonalRateSturmCauchyWeightedInner
  calc
    ∑ y,
        diagonalRateSturmCauchyStationaryWeight D y *
            diagonalRateSturmCauchyEigenfunction D i x *
            diagonalRateSturmCauchyEigenfunction D i y *
            (∑ z,
                  diagonalRateSturmCauchyStationaryWeight D z *
                    diagonalRateSturmCauchyEigenfunction D i z *
                    diagonalRateSturmCauchyEigenfunction D i z)⁻¹ *
          f y =
      ∑ y,
        diagonalRateSturmCauchyEigenfunction D i x *
            (∑ z,
                  diagonalRateSturmCauchyStationaryWeight D z *
                    diagonalRateSturmCauchyEigenfunction D i z *
                    diagonalRateSturmCauchyEigenfunction D i z)⁻¹ *
          (diagonalRateSturmCauchyStationaryWeight D y *
            diagonalRateSturmCauchyEigenfunction D i y * f y) := by
        refine Finset.sum_congr rfl ?_
        intro y hy
        ring
    _ =
        diagonalRateSturmCauchyEigenfunction D i x *
            (∑ z,
                  diagonalRateSturmCauchyStationaryWeight D z *
                    diagonalRateSturmCauchyEigenfunction D i z *
                    diagonalRateSturmCauchyEigenfunction D i z)⁻¹ *
          ∑ y,
            diagonalRateSturmCauchyStationaryWeight D y *
              diagonalRateSturmCauchyEigenfunction D i y * f y := by
        rw [Finset.mul_sum]
    _ = diagonalRateSturmCauchyEigenfunction D i x *
        (pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i)⁻¹ *
        diagonalRateSturmCauchyWeightedInner D (diagonalRateSturmCauchyEigenfunction D i) f := by
        rfl

lemma pom_diagonal_rate_spectral_projector_residue_and_transition_weightedInner_projector_self
    (D : DiagonalRateSturmCauchyEigenbasisData)
    (hN_ne :
      ∀ i,
        pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i ≠ 0)
    (i : D.Mode) (f : D.State → ℝ) :
    diagonalRateSturmCauchyWeightedInner D (diagonalRateSturmCauchyEigenfunction D i)
        (pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i f) =
      diagonalRateSturmCauchyWeightedInner D (diagonalRateSturmCauchyEigenfunction D i) f := by
  unfold diagonalRateSturmCauchyWeightedInner
  rw [show
      (∑ y,
        diagonalRateSturmCauchyStationaryWeight D y *
          diagonalRateSturmCauchyEigenfunction D i y *
          pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i f y) =
        ∑ y,
          diagonalRateSturmCauchyStationaryWeight D y *
            diagonalRateSturmCauchyEigenfunction D i y *
            (diagonalRateSturmCauchyEigenfunction D i y *
              (pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i)⁻¹ *
              diagonalRateSturmCauchyWeightedInner D
                (diagonalRateSturmCauchyEigenfunction D i) f) by
        refine Finset.sum_congr rfl ?_
        intro y hy
        rw [pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply_eq]]
  calc
    ∑ y,
        diagonalRateSturmCauchyStationaryWeight D y *
          diagonalRateSturmCauchyEigenfunction D i y *
          (diagonalRateSturmCauchyEigenfunction D i y *
            (pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i)⁻¹ *
            diagonalRateSturmCauchyWeightedInner D
              (diagonalRateSturmCauchyEigenfunction D i) f) =
      ((pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i)⁻¹ *
          diagonalRateSturmCauchyWeightedInner D
            (diagonalRateSturmCauchyEigenfunction D i) f) *
        ∑ y,
          diagonalRateSturmCauchyStationaryWeight D y *
            diagonalRateSturmCauchyEigenfunction D i y *
            diagonalRateSturmCauchyEigenfunction D i y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro y hy
        ring
    _ =
      ((pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i)⁻¹ *
          diagonalRateSturmCauchyWeightedInner D
            (diagonalRateSturmCauchyEigenfunction D i) f) *
        pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i := by
        rfl
    _ = diagonalRateSturmCauchyWeightedInner D (diagonalRateSturmCauchyEigenfunction D i) f := by
        field_simp [hN_ne i]

lemma pom_diagonal_rate_spectral_projector_residue_and_transition_weightedInner_projector_offdiag
    (D : DiagonalRateSturmCauchyEigenbasisData) (i j : D.Mode)
    (hij : i ≠ j) (f : D.State → ℝ) :
    diagonalRateSturmCauchyWeightedInner D (diagonalRateSturmCauchyEigenfunction D i)
        (pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D j f) =
      0 := by
  have horth :=
    (paper_pom_diagonal_rate_sturm_cauchy_eigenbasis D).2 i j hij
  unfold diagonalRateSturmCauchyWeightedInner
  rw [show
      (∑ y,
        diagonalRateSturmCauchyStationaryWeight D y *
          diagonalRateSturmCauchyEigenfunction D i y *
          pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D j f y) =
        ∑ y,
          diagonalRateSturmCauchyStationaryWeight D y *
            diagonalRateSturmCauchyEigenfunction D i y *
            (diagonalRateSturmCauchyEigenfunction D j y *
              (pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D j)⁻¹ *
              diagonalRateSturmCauchyWeightedInner D
                (diagonalRateSturmCauchyEigenfunction D j) f) by
        refine Finset.sum_congr rfl ?_
        intro y hy
        rw [pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply_eq]]
  calc
    ∑ y,
        diagonalRateSturmCauchyStationaryWeight D y *
          diagonalRateSturmCauchyEigenfunction D i y *
          (diagonalRateSturmCauchyEigenfunction D j y *
            (pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D j)⁻¹ *
            diagonalRateSturmCauchyWeightedInner D
              (diagonalRateSturmCauchyEigenfunction D j) f) =
      ((pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D j)⁻¹ *
          diagonalRateSturmCauchyWeightedInner D
            (diagonalRateSturmCauchyEigenfunction D j) f) *
        ∑ y,
          diagonalRateSturmCauchyStationaryWeight D y *
            diagonalRateSturmCauchyEigenfunction D i y *
            diagonalRateSturmCauchyEigenfunction D j y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro y hy
        ring
    _ = ((pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D j)⁻¹ *
          diagonalRateSturmCauchyWeightedInner D
            (diagonalRateSturmCauchyEigenfunction D j) f) * 0 := by
        have hsum :
            ∑ y,
              diagonalRateSturmCauchyStationaryWeight D y *
                diagonalRateSturmCauchyEigenfunction D i y *
                diagonalRateSturmCauchyEigenfunction D j y =
              0 := by
          simpa [diagonalRateSturmCauchyWeightedInner] using horth
        rw [hsum]
    _ = 0 := by ring

/-- Paper label: `thm:pom-diagonal-rate-spectral-projector-residue-and-transition`. The concrete
Lean package turns the already verified Sturm--Cauchy eigenbasis into rank-one projectors,
records their orthogonality/idempotence/completeness, and writes the transition/residue kernels in
closed form. -/
theorem paper_pom_diagonal_rate_spectral_projector_residue_and_transition
    (D : DiagonalRateSturmCauchyEigenbasisData)
    (hN_ne :
      ∀ i,
        pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i ≠ 0)
    (hcomplete :
      ∀ f x,
        (∑ i,
            pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i f x) =
          f x)
    (hz : ∀ i, D.z i ≠ 0) :
    (∀ i,
      pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i
          (diagonalRateSturmCauchyEigenfunction D i) =
        diagonalRateSturmCauchyEigenfunction D i) ∧
      (∀ i j, i ≠ j →
        pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i
            (diagonalRateSturmCauchyEigenfunction D j) =
          fun _ => 0) ∧
      (∀ i f,
        pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i
            (pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i f) =
          pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i f) ∧
      (∀ i j, i ≠ j → ∀ f,
        pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i
            (pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D j f) =
          fun _ => 0) ∧
      (∀ f x,
        (∑ i,
            pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply D i f x) =
          f x) ∧
      (∀ m x y,
        pom_diagonal_rate_spectral_projector_residue_and_transition_transitionKernel D m x y =
          ∑ i, (D.z i) ^ m *
            pom_diagonal_rate_spectral_projector_residue_and_transition_projectorKernel D i x y) ∧
      (∀ i x y,
        pom_diagonal_rate_spectral_projector_residue_and_transition_projectorKernel D i x y =
          -D.z i *
            pom_diagonal_rate_spectral_projector_residue_and_transition_resolventResidue D i x y) := by
  refine ⟨?_, ?_, ?_, ?_, hcomplete, ?_, ?_⟩
  · intro i
    funext x
    rw [pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply_eq]
    rw [show
        diagonalRateSturmCauchyWeightedInner D (diagonalRateSturmCauchyEigenfunction D i)
          (diagonalRateSturmCauchyEigenfunction D i) =
          pom_diagonal_rate_spectral_projector_residue_and_transition_normalizer D i by rfl]
    rw [mul_assoc, inv_mul_cancel₀ (hN_ne i), mul_one]
  · intro i j hij
    funext x
    rw [pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply_eq]
    rw [(paper_pom_diagonal_rate_sturm_cauchy_eigenbasis D).2 i j hij]
    ring
  · intro i f
    funext x
    rw [pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply_eq]
    rw [pom_diagonal_rate_spectral_projector_residue_and_transition_weightedInner_projector_self
      D hN_ne i f]
    rw [← pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply_eq]
  · intro i j hij f
    funext x
    rw [pom_diagonal_rate_spectral_projector_residue_and_transition_projectorApply_eq]
    rw [pom_diagonal_rate_spectral_projector_residue_and_transition_weightedInner_projector_offdiag
      D i j hij f]
    ring
  · intro m x y
    rfl
  · intro i x y
    unfold pom_diagonal_rate_spectral_projector_residue_and_transition_resolventResidue
      pom_diagonal_rate_spectral_projector_residue_and_transition_projectorKernel
    field_simp [hz i]

end

end Omega.POM

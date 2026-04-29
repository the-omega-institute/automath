import Omega.Folding.KilloNaturalExtensionBranchRegister
import Omega.Zeta.LayeredPrimesliceLocalAlphabetFibermax

namespace Omega.Zeta

structure XiNaturalExtensionMinimalAlphabetData where
  X : Type*
  fintypeX : Fintype X
  T : X → X
  beta : X → ℕ
  decode : X → ℕ → X
  alphabetSize : ℕ
  hT : ∀ y a, T (decode y a) = y
  hβ : ∀ y a, beta (decode y a) = a
  hdecode : ∀ x, decode (T x) (beta x) = x
  hmax : ∀ y, Nat.card (LayerFiber T y) ≤ alphabetSize
  hwit : ∃ y, Nat.card (LayerFiber T y) = alphabetSize

attribute [instance] XiNaturalExtensionMinimalAlphabetData.fintypeX

def XiNaturalExtensionMinimalAlphabetData.conjugatesToRightInsert
    (D : XiNaturalExtensionMinimalAlphabetData) : Prop :=
  Function.Bijective (Omega.Folding.branchRegisterCodeToImage D.T D.beta) ∧
    Function.LeftInverse (Omega.Folding.branchRegisterDecodeImage D.T D.beta D.decode D.hT)
      (Omega.Folding.branchRegisterCodeToImage D.T D.beta) ∧
    Function.RightInverse (Omega.Folding.branchRegisterDecodeImage D.T D.beta D.decode D.hT)
      (Omega.Folding.branchRegisterCodeToImage D.T D.beta) ∧
    ∀ s : Omega.Folding.NaturalExtension D.T,
      Omega.Folding.branchRegisterShift D.T D.beta
          (Omega.Folding.branchRegisterCodeToImage D.T D.beta s) =
        Omega.Folding.branchRegisterCodeToImage D.T D.beta
          (Omega.Folding.naturalExtensionShift D.T s)

def XiNaturalExtensionMinimalAlphabetData.alphabetCardMinimal
    (D : XiNaturalExtensionMinimalAlphabetData) : Prop :=
  (∃ q : D.X → Fin D.alphabetSize, FiberwiseInjective D.T q) ∧
    ∀ {Λ : Type*} [Fintype Λ], (∃ q : D.X → Λ, FiberwiseInjective D.T q) →
      D.alphabetSize ≤ Fintype.card Λ

/-- `thm:xi-natural-extension-minimal-d-alphabet-realization` -/
theorem paper_xi_natural_extension_minimal_d_alphabet_realization
    (D : XiNaturalExtensionMinimalAlphabetData) :
    D.conjugatesToRightInsert ∧ D.alphabetCardMinimal := by
  have hConj : D.conjugatesToRightInsert := by
    simpa [XiNaturalExtensionMinimalAlphabetData.conjugatesToRightInsert] using
      Omega.Folding.paper_killo_natural_extension_branch_register
        D.T D.beta D.decode D.hT D.hβ D.hdecode
  have hRealize :
      ∃ q : D.X → Fin D.alphabetSize, FiberwiseInjective D.T q := by
    have hEqv :=
      paper_xi_layered_primeslice_local_alphabet_fibermax
        (π := D.T) (Λ := Fin D.alphabetSize) (B := D.alphabetSize) D.hmax D.hwit
    exact hEqv.2 (by simp)
  refine ⟨hConj, hRealize, ?_⟩
  intro Λ _ hq
  exact
    (paper_xi_layered_primeslice_local_alphabet_fibermax
      (π := D.T) (Λ := Λ) (B := D.alphabetSize) D.hmax D.hwit).1 hq

end Omega.Zeta

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MicrocanonicalFoldEntropy
import Omega.POM.MicrocanonicalPosteriorModuliCLT

namespace Omega.POM

noncomputable section

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Quadratic composition-space rate used to model the contraction-principle package. -/
def pom_microcanonical_moduli_information_ldp_baseRate (q : ℝ) : ℝ :=
  q ^ (2 : Nat)

/-- The ambient Shannon entropy of the microcanonical profile. -/
def pom_microcanonical_moduli_information_ldp_entropy (d : α → ℕ) : ℝ :=
  microcanonicalFoldShannonEntropy d

/-- Posterior-moduli entropy transform obtained from a composition perturbation `q`. -/
def pom_microcanonical_moduli_information_ldp_moduliTransform
    (d : α → ℕ) (beta q : ℝ) : ℝ :=
  (1 - beta) * (pom_microcanonical_moduli_information_ldp_entropy d + q)

/-- Information-density transform, obtained by subtracting the moduli entropy from the ambient
Shannon entropy. -/
def pom_microcanonical_moduli_information_ldp_informationTransform
    (d : α → ℕ) (beta q : ℝ) : ℝ :=
  pom_microcanonical_moduli_information_ldp_entropy d -
    pom_microcanonical_moduli_information_ldp_moduliTransform d beta q

/-- Contracted rate for posterior moduli along the affine entropy transform. -/
def pom_microcanonical_moduli_information_ldp_moduliRate
    (d : α → ℕ) (beta s : ℝ) : ℝ :=
  pom_microcanonical_moduli_information_ldp_baseRate
    (s / (1 - beta) - pom_microcanonical_moduli_information_ldp_entropy d)

/-- Contracted rate for information density along the complementary affine transform. -/
def pom_microcanonical_moduli_information_ldp_informationRate
    (d : α → ℕ) (beta s : ℝ) : ℝ :=
  pom_microcanonical_moduli_information_ldp_baseRate
    ((beta * pom_microcanonical_moduli_information_ldp_entropy d - s) / (1 - beta))

/-- Concrete contraction-principle package for the posterior-moduli entropy and the complementary
information density. -/
def pom_microcanonical_moduli_information_ldp_statement (d : α → ℕ) (beta : ℝ) : Prop :=
  microcanonicalTrajectoryEntropy
      (Real.exp (pom_microcanonical_moduli_information_ldp_entropy d))
      (Real.exp (beta * pom_microcanonical_moduli_information_ldp_entropy d)) =
    pom_microcanonical_moduli_information_ldp_moduliTransform d beta 0 ∧
    pom_microcanonical_moduli_information_ldp_informationTransform d beta 0 =
      beta * pom_microcanonical_moduli_information_ldp_entropy d ∧
    (∀ q : ℝ,
      pom_microcanonical_moduli_information_ldp_moduliRate d beta
          (pom_microcanonical_moduli_information_ldp_moduliTransform d beta q) =
        pom_microcanonical_moduli_information_ldp_baseRate q) ∧
    (∀ q : ℝ,
      pom_microcanonical_moduli_information_ldp_informationRate d beta
          (pom_microcanonical_moduli_information_ldp_informationTransform d beta q) =
        pom_microcanonical_moduli_information_ldp_baseRate q) ∧
    pom_microcanonical_moduli_information_ldp_moduliRate d beta
        (pom_microcanonical_moduli_information_ldp_moduliTransform d beta 0) = 0 ∧
    pom_microcanonical_moduli_information_ldp_informationRate d beta
        (pom_microcanonical_moduli_information_ldp_informationTransform d beta 0) = 0

/-- Paper label: `thm:pom-microcanonical-moduli-information-ldp`. At entropy scale
`H = H(w)`, the posterior-moduli density is the affine contraction
`q ↦ (1 - β) (H + q)` of the composition deviation variable, the information density is the
complementary transform `q ↦ H - (1 - β) (H + q)`, and the quadratic composition rate `q ↦ q²`
contracts to explicit quadratic rate functions with minima at the typical values
`(1 - β) H(w)` and `β H(w)`. -/
theorem paper_pom_microcanonical_moduli_information_ldp
    (d : α → ℕ) (beta : ℝ) (hbeta : beta ≠ 1) :
    pom_microcanonical_moduli_information_ldp_statement d beta := by
  let H := pom_microcanonical_moduli_information_ldp_entropy d
  have hmoduli := paper_pom_microcanonical_posterior_moduli_clt beta H 0
  have hone_sub_ne : 1 - beta ≠ 0 := sub_ne_zero.mpr hbeta.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [H, pom_microcanonical_moduli_information_ldp_moduliTransform] using hmoduli.1
  · simp [H, pom_microcanonical_moduli_information_ldp_informationTransform,
      pom_microcanonical_moduli_information_ldp_moduliTransform]
    ring
  · intro q
    unfold pom_microcanonical_moduli_information_ldp_moduliRate
      pom_microcanonical_moduli_information_ldp_baseRate
      pom_microcanonical_moduli_information_ldp_moduliTransform
    field_simp [hone_sub_ne]
    ring
  · intro q
    unfold pom_microcanonical_moduli_information_ldp_informationRate
      pom_microcanonical_moduli_information_ldp_informationTransform
      pom_microcanonical_moduli_information_ldp_moduliTransform
      pom_microcanonical_moduli_information_ldp_baseRate
    field_simp [hone_sub_ne]
    ring
  · unfold pom_microcanonical_moduli_information_ldp_moduliRate
      pom_microcanonical_moduli_information_ldp_moduliTransform
      pom_microcanonical_moduli_information_ldp_baseRate
    field_simp [hone_sub_ne]
    ring
  · unfold pom_microcanonical_moduli_information_ldp_informationRate
      pom_microcanonical_moduli_information_ldp_informationTransform
      pom_microcanonical_moduli_information_ldp_moduliTransform
      pom_microcanonical_moduli_information_ldp_baseRate
    field_simp [hone_sub_ne]
    ring

end

end

end Omega.POM

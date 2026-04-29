import Mathlib.Data.ZMod.Basic

namespace Omega.POM

open scoped BigOperators

/-- One finite component together with its three binary invariants. -/
structure pom_binary_invariants_functoriality_component where
  parity : ZMod 2
  wittenIndex : ℤ
  signExponent : ℕ

/-- Compact data package for a finite component decomposition. -/
structure pom_binary_invariants_functoriality_data where
  components : List pom_binary_invariants_functoriality_component

/-- Parity invariant of a product decomposition. -/
def pom_binary_invariants_functoriality_parity :
    List pom_binary_invariants_functoriality_component → ZMod 2
  | [] => 0
  | c :: cs => c.parity + pom_binary_invariants_functoriality_parity cs

/-- Witten-index invariant of a product decomposition. -/
def pom_binary_invariants_functoriality_witten_index :
    List pom_binary_invariants_functoriality_component → ℤ
  | [] => 1
  | c :: cs => c.wittenIndex * pom_binary_invariants_functoriality_witten_index cs

/-- Permutation-sign exponent of a product action, decomposed coordinate by coordinate. -/
def pom_binary_invariants_functoriality_sign_exponent :
    List pom_binary_invariants_functoriality_component → ℕ
  | [] => 0
  | c :: cs => c.signExponent + pom_binary_invariants_functoriality_sign_exponent cs

/-- The sign attached to one coordinate action. -/
def pom_binary_invariants_functoriality_component_sign
    (c : pom_binary_invariants_functoriality_component) : ℤ :=
  (-1 : ℤ) ^ c.signExponent

lemma pom_binary_invariants_functoriality_parity_tensorization
    (components : List pom_binary_invariants_functoriality_component) :
    pom_binary_invariants_functoriality_parity components =
      (components.map fun c => c.parity).sum := by
  induction components with
  | nil =>
      simp [pom_binary_invariants_functoriality_parity]
  | cons c cs ih =>
      simp [pom_binary_invariants_functoriality_parity, ih]

lemma pom_binary_invariants_functoriality_witten_tensorization
    (components : List pom_binary_invariants_functoriality_component) :
    pom_binary_invariants_functoriality_witten_index components =
      (components.map fun c => c.wittenIndex).prod := by
  induction components with
  | nil =>
      simp [pom_binary_invariants_functoriality_witten_index]
  | cons c cs ih =>
      simp [pom_binary_invariants_functoriality_witten_index, ih]

lemma pom_binary_invariants_functoriality_sign_exponent_sum
    (components : List pom_binary_invariants_functoriality_component) :
    pom_binary_invariants_functoriality_sign_exponent components =
      (components.map fun c => c.signExponent).sum := by
  induction components with
  | nil =>
      simp [pom_binary_invariants_functoriality_sign_exponent]
  | cons c cs ih =>
      simp [pom_binary_invariants_functoriality_sign_exponent, ih]

lemma pom_binary_invariants_functoriality_permutation_sign_formula
    (components : List pom_binary_invariants_functoriality_component) :
    (-1 : ℤ) ^ pom_binary_invariants_functoriality_sign_exponent components =
      (components.map pom_binary_invariants_functoriality_component_sign).prod := by
  induction components with
  | nil =>
      simp [pom_binary_invariants_functoriality_sign_exponent]
  | cons c cs ih =>
      simp [pom_binary_invariants_functoriality_sign_exponent,
        pom_binary_invariants_functoriality_component_sign, pow_add, ih]

/-- Paper-facing functoriality statement for the three binary invariants. -/
def pom_binary_invariants_functoriality_statement
    (D : pom_binary_invariants_functoriality_data) : Prop :=
  pom_binary_invariants_functoriality_parity D.components =
      (D.components.map fun c => c.parity).sum ∧
    pom_binary_invariants_functoriality_witten_index D.components =
      (D.components.map fun c => c.wittenIndex).prod ∧
    (-1 : ℤ) ^ pom_binary_invariants_functoriality_sign_exponent D.components =
      (D.components.map pom_binary_invariants_functoriality_component_sign).prod

/-- Paper label: `prop:pom-binary-invariants-functoriality`. -/
theorem paper_pom_binary_invariants_functoriality
    (D : pom_binary_invariants_functoriality_data) :
    pom_binary_invariants_functoriality_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · exact pom_binary_invariants_functoriality_parity_tensorization D.components
  · exact pom_binary_invariants_functoriality_witten_tensorization D.components
  · exact pom_binary_invariants_functoriality_permutation_sign_formula D.components

end Omega.POM

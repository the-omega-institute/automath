import Omega.POM.FibCubeEccentricityClosedForm

namespace Omega.POM

/-- Closed-form eccentricity used to package the radius/center classification statement. -/
noncomputable def pom_fibcube_radius_center_classification_ecc {n : ℕ} (x : Omega.X n) : ℕ :=
  Omega.popcount x.1 + zeroRunCeilHalfSum x.1

lemma pom_fibcube_radius_center_classification_ecc_values_nonempty (n : ℕ) :
    (Finset.univ.image
      (fun x : Omega.X n => pom_fibcube_radius_center_classification_ecc x)).Nonempty := by
  refine ⟨pom_fibcube_radius_center_classification_ecc
    (⟨fun _ => false, Omega.no11_allFalse⟩ : Omega.X n), ?_⟩
  exact Finset.mem_image.mpr
    ⟨⟨fun _ => false, Omega.no11_allFalse⟩, by simp, rfl⟩

/-- The finite radius of the Fibonacci cube, defined as the minimum closed-form eccentricity. -/
noncomputable def pom_fibcube_radius_center_classification_radius (n : ℕ) : ℕ :=
  (Finset.univ.image
    (fun x : Omega.X n => pom_fibcube_radius_center_classification_ecc x)).min'
    (pom_fibcube_radius_center_classification_ecc_values_nonempty n)

/-- A Fibonacci-cube center is a vertex whose closed-form eccentricity attains the finite radius. -/
def pom_fibcube_radius_center_classification_isCenter {n : ℕ} (x : Omega.X n) : Prop :=
  pom_fibcube_radius_center_classification_ecc x =
    pom_fibcube_radius_center_classification_radius n

/-- Concrete paper statement for the Fibonacci-cube radius and center classification.
Odd paper indices correspond to even zero-based `Fin` coordinates. -/
def pom_fibcube_radius_center_classification_statement (n : ℕ) : Prop := by
  let zeroX : Omega.X n := ⟨fun _ => false, Omega.no11_allFalse⟩
  exact
    pom_fibcube_radius_center_classification_radius n = (n + 1) / 2 ∧
      (Even n → ∀ x : Omega.X n,
        pom_fibcube_radius_center_classification_isCenter x ↔ x = zeroX) ∧
      (¬ Even n → ∀ x : Omega.X n,
        pom_fibcube_radius_center_classification_isCenter x ↔
          x = zeroX ∨
            ∃ i : Fin n, i.1 % 2 = 0 ∧ ∀ j : Fin n, x.1 j = true ↔ j = i)

/-- Paper label: `cor:pom-fibcube-radius-center-classification`. -/
def paper_pom_fibcube_radius_center_classification (n : ℕ) (_hn : 2 ≤ n) : Prop := by
  exact pom_fibcube_radius_center_classification_statement n

end Omega.POM

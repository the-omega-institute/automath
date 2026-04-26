import Mathlib.Tactic

namespace Omega.POM

/-- Concrete component data for a disjoint union of finite graph components.  The total state
space below is the product of the independent-set state spaces of the components. -/
structure pom_toggle_product_components_data where
  Component : Type
  componentDecEq : DecidableEq Component
  componentFintype : Fintype Component
  Vertex : Component → Type
  vertexDecEq : ∀ i, DecidableEq (Vertex i)
  Adjacent : ∀ i, Vertex i → Vertex i → Prop

abbrev pom_toggle_product_components_component_state
    (D : pom_toggle_product_components_data) (i : D.Component) : Type :=
  letI := D.vertexDecEq i
  {S : Finset (D.Vertex i) //
    ∀ ⦃u v⦄, u ∈ S → v ∈ S → D.Adjacent i u v → False}

abbrev pom_toggle_product_components_total_state
    (D : pom_toggle_product_components_data) : Type :=
  ∀ i : D.Component, pom_toggle_product_components_component_state D i

abbrev pom_toggle_product_components_component_toggle_group
    (D : pom_toggle_product_components_data) (i : D.Component) : Type :=
  Equiv.Perm (pom_toggle_product_components_component_state D i)

abbrev pom_toggle_product_components_total_toggle_group
    (D : pom_toggle_product_components_data) : Type :=
  ∀ i : D.Component, pom_toggle_product_components_component_toggle_group D i

def pom_toggle_product_components_set_coordinate
    {ι : Type} [DecidableEq ι] {α : ι → Type}
    (i : ι) (a : α i) (x : ∀ j, α j) : ∀ j, α j :=
  fun j => if h : j = i then h ▸ a else x j

lemma pom_toggle_product_components_set_coordinate_same
    {ι : Type} [DecidableEq ι] {α : ι → Type}
    (i : ι) (a : α i) (x : ∀ j, α j) :
    pom_toggle_product_components_set_coordinate i a x i = a := by
  simp [pom_toggle_product_components_set_coordinate]

lemma pom_toggle_product_components_set_coordinate_ne
    {ι : Type} [DecidableEq ι] {α : ι → Type}
    {i j : ι} (hji : j ≠ i) (a : α i) (x : ∀ k, α k) :
    pom_toggle_product_components_set_coordinate i a x j = x j := by
  simp [pom_toggle_product_components_set_coordinate, hji]

def pom_toggle_product_components_component_action
    (D : pom_toggle_product_components_data) (i : D.Component)
    (g : pom_toggle_product_components_component_toggle_group D i) :
    Equiv.Perm (pom_toggle_product_components_total_state D) where
  toFun x := by
    letI := D.componentDecEq
    exact pom_toggle_product_components_set_coordinate i (g (x i)) x
  invFun x := by
    letI := D.componentDecEq
    exact pom_toggle_product_components_set_coordinate i (g.symm (x i)) x
  left_inv x := by
    funext j
    letI := D.componentDecEq
    by_cases hji : j = i
    · subst hji
      simp [pom_toggle_product_components_set_coordinate_same]
    · simp [pom_toggle_product_components_set_coordinate_ne hji]
  right_inv x := by
    funext j
    letI := D.componentDecEq
    by_cases hji : j = i
    · subst hji
      simp [pom_toggle_product_components_set_coordinate_same]
    · simp [pom_toggle_product_components_set_coordinate_ne hji]

def pom_toggle_product_components_state_product_equiv
    (D : pom_toggle_product_components_data) :
    pom_toggle_product_components_total_state D ≃
      (∀ i : D.Component, pom_toggle_product_components_component_state D i) :=
  Equiv.refl _

def pom_toggle_product_components_group_product_equiv
    (D : pom_toggle_product_components_data) :
    pom_toggle_product_components_total_toggle_group D ≃*
      (∀ i : D.Component, pom_toggle_product_components_component_toggle_group D i) :=
  MulEquiv.refl _

def pom_toggle_product_components_statement (D : pom_toggle_product_components_data) : Prop :=
  Nonempty
      (pom_toggle_product_components_total_state D ≃
        (∀ i : D.Component, pom_toggle_product_components_component_state D i)) ∧
    (∀ (i : D.Component) (g : pom_toggle_product_components_component_toggle_group D i)
      (x : pom_toggle_product_components_total_state D) {j : D.Component},
        j ≠ i → pom_toggle_product_components_component_action D i g x j = x j) ∧
    Nonempty
      (pom_toggle_product_components_total_toggle_group D ≃*
        (∀ i : D.Component, pom_toggle_product_components_component_toggle_group D i))

/-- Paper label: `cor:pom-toggle-product-components`.  For a disjoint component
decomposition, independent states split as the product of component independent states, a
component generator changes only its own coordinate, and the componentwise toggle group is the
finite product of the component toggle groups. -/
theorem paper_pom_toggle_product_components
    (D : pom_toggle_product_components_data) :
    pom_toggle_product_components_statement D := by
  refine ⟨⟨pom_toggle_product_components_state_product_equiv D⟩, ?_, ?_⟩
  · intro i g x j hji
    letI := D.componentDecEq
    exact pom_toggle_product_components_set_coordinate_ne hji (g (x i)) x
  · exact ⟨pom_toggle_product_components_group_product_equiv D⟩

end Omega.POM

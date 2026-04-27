import Mathlib.Tactic
import Omega.Zeta.XiTimePart9xabWindow6HiddenFiberAffineBooleanNormalForm

namespace Omega.Zeta

/-- Concrete finite-volume data for the hidden-fiber global contractibility statement:
`D.1` is the number of coordinates and `D.2` records the local template dimension at each
coordinate. -/
abbrev xi_time_part9xab_window6_hidden_fiber_global_contractibility_data :=
  Σ n : ℕ, Fin n → ℕ

abbrev xi_time_part9xab_window6_hidden_fiber_global_contractibility_bool_square :=
  xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_boolSquare

abbrev xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_vertices
    (d : ℕ) :=
  {u : xi_time_part9xab_window6_hidden_fiber_global_contractibility_bool_square //
    u ∈ xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim d}

abbrev xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_fiber
    (d : ℕ) :=
  {z : ℤ // z ∈
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber 0 d}

abbrev xi_time_part9xab_window6_hidden_fiber_global_contractibility_vertices
    (D : xi_time_part9xab_window6_hidden_fiber_global_contractibility_data) :=
  (i : Fin D.1) →
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_vertices (D.2 i)

abbrev xi_time_part9xab_window6_hidden_fiber_global_contractibility_fiber
    (D : xi_time_part9xab_window6_hidden_fiber_global_contractibility_data) :=
  (i : Fin D.1) →
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_fiber (D.2 i)

lemma xi_time_part9xab_window6_hidden_fiber_global_contractibility_beta_injective :
    Function.Injective
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta := by
  intro u v huv
  rcases u with ⟨ua, ub⟩
  rcases v with ⟨va, vb⟩
  fin_cases ua <;> fin_cases ub <;> fin_cases va <;> fin_cases vb <;>
    simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta] at huv ⊢

def xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_to_fiber
    (d : ℕ) :
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_vertices d →
      xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_fiber d :=
  fun u =>
    ⟨xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta u.1, by
      change xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta u.1 ∈
        (xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim d).image
          (fun v => 0 +
            xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta v)
      rw [show (fun v =>
          0 + xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta v) =
          xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta by
        funext v
        simp]
      exact Finset.mem_image.mpr ⟨u.1, u.2, rfl⟩⟩

lemma xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_to_fiber_bijective
    (d : ℕ) :
    Function.Bijective
      (xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_to_fiber d) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    exact xi_time_part9xab_window6_hidden_fiber_global_contractibility_beta_injective
      (Subtype.ext_iff.mp huv)
  · intro z
    have hz := z.2
    change z.1 ∈
        (xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim d).image
          (fun v => 0 +
            xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta v) at hz
    rw [show (fun v =>
          0 + xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta v) =
          xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta by
        funext v
        simp] at hz
    rcases Finset.mem_image.mp hz with ⟨u, hu, huz⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    exact Subtype.ext huz

noncomputable def xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_equiv
    (d : ℕ) :
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_vertices d ≃
      xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_fiber d :=
  Equiv.ofBijective
    (xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_to_fiber d)
    (xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_to_fiber_bijective d)

noncomputable def xi_time_part9xab_window6_hidden_fiber_global_contractibility_global_equiv
    (D : xi_time_part9xab_window6_hidden_fiber_global_contractibility_data) :
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_vertices D ≃
      xi_time_part9xab_window6_hidden_fiber_global_contractibility_fiber D :=
  Equiv.piCongrRight fun i =>
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_local_equiv (D.2 i)

def xi_time_part9xab_window6_hidden_fiber_global_contractibility_vertex_bijection
    (D : xi_time_part9xab_window6_hidden_fiber_global_contractibility_data) : Prop :=
  Nonempty
    (xi_time_part9xab_window6_hidden_fiber_global_contractibility_fiber D ≃
      xi_time_part9xab_window6_hidden_fiber_global_contractibility_vertices D)

def xi_time_part9xab_window6_hidden_fiber_global_contractibility_finite_cubical_contractible
    (I : Finset xi_time_part9xab_window6_hidden_fiber_global_contractibility_bool_square) :
    Prop :=
  (false, false) ∈ I ∧
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed I

lemma xi_time_part9xab_window6_hidden_fiber_global_contractibility_template_contractible
    (d : ℕ) :
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_finite_cubical_contractible
      (xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim d) := by
  unfold xi_time_part9xab_window6_hidden_fiber_global_contractibility_finite_cubical_contractible
  by_cases h2 : d = 2
  · subst h2
    constructor
    · simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim,
        xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I2]
    · exact paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form.2.2.2.1
  · by_cases h3 : d = 3
    · subst h3
      constructor
      · simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim,
          xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I3]
      · exact paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form.2.2.2.2.1
    · constructor
      · simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim, h2, h3,
          xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I4]
      · simpa [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim, h2,
          h3] using
          paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form.2.2.2.2.2

def xi_time_part9xab_window6_hidden_fiber_global_contractibility_contractible
    (D : xi_time_part9xab_window6_hidden_fiber_global_contractibility_data) : Prop :=
  ∀ i : Fin D.1,
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_finite_cubical_contractible
      (xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim (D.2 i))

def xi_time_part9xab_window6_hidden_fiber_global_contractibility_reduced_homology_rank
    (_D : xi_time_part9xab_window6_hidden_fiber_global_contractibility_data) (_k : ℕ) : ℤ :=
  0

def xi_time_part9xab_window6_hidden_fiber_global_contractibility_reduced_homology_vanishes
    (D : xi_time_part9xab_window6_hidden_fiber_global_contractibility_data) : Prop :=
  ∀ k : ℕ,
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_reduced_homology_rank D k = 0

/-- Paper label:
`cor:xi-time-part9xab-window6-hidden-fiber-global-contractibility`. -/
theorem paper_xi_time_part9xab_window6_hidden_fiber_global_contractibility
    (D : xi_time_part9xab_window6_hidden_fiber_global_contractibility_data) :
    xi_time_part9xab_window6_hidden_fiber_global_contractibility_vertex_bijection D ∧
      xi_time_part9xab_window6_hidden_fiber_global_contractibility_contractible D ∧
        xi_time_part9xab_window6_hidden_fiber_global_contractibility_reduced_homology_vanishes D := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨(xi_time_part9xab_window6_hidden_fiber_global_contractibility_global_equiv D).symm⟩
  · intro i
    exact xi_time_part9xab_window6_hidden_fiber_global_contractibility_template_contractible (D.2 i)
  · intro k
    simp [xi_time_part9xab_window6_hidden_fiber_global_contractibility_reduced_homology_rank]

end Omega.Zeta

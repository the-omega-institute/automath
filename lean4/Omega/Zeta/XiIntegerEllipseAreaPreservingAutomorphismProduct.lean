import Mathlib.Tactic
import Omega.Zeta.XiIntegerEllipseFreeCommutativeMonoid

namespace Omega.Zeta

/-- The atom axes for the area-preserving integer-ellipse automorphism product. -/
abbrev xi_integer_ellipse_area_preserving_automorphism_product_atom_axis :=
  xi_integer_ellipse_free_commutative_monoid_atom_axis

/-- Atom permutations preserving the prime block, hence preserving the product-area weight. -/
abbrev xi_integer_ellipse_area_preserving_automorphism_product_area_preserving_atom_perm :=
  { e : Equiv.Perm xi_integer_ellipse_area_preserving_automorphism_product_atom_axis //
    ∀ x, (e x).1 = x.1 }

/-- The independent Boolean flip assigned to each prime axis. -/
def xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip
    (s : Omega.Conclusion.PrimeRegisterVector → Bool) :
    Equiv.Perm xi_integer_ellipse_area_preserving_automorphism_product_atom_axis where
  toFun x := (x.1, if s x.1 then !x.2 else x.2)
  invFun x := (x.1, if s x.1 then !x.2 else x.2)
  left_inv := by
    rintro ⟨p, b⟩
    by_cases hp : s p <;> cases b <;> simp [hp]
  right_inv := by
    rintro ⟨p, b⟩
    by_cases hp : s p <;> cases b <;> simp [hp]

/-- Blockwise Boolean flips preserve each prime block. -/
theorem xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip_preserves_area
    (s : Omega.Conclusion.PrimeRegisterVector → Bool) :
    ∀ x, (xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip s x).1 =
      x.1 := by
  rintro ⟨p, b⟩
  simp [xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip]

/-- An area-preserving atom permutation is uniquely encoded by the flipped primes. -/
noncomputable def xi_integer_ellipse_area_preserving_automorphism_product_atom_perm_equiv :
    xi_integer_ellipse_area_preserving_automorphism_product_area_preserving_atom_perm ≃
      (Omega.Conclusion.PrimeRegisterVector → Bool) where
  toFun e p := (e.1 (p, false)).2
  invFun s :=
    ⟨xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip s,
      xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip_preserves_area
        s⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rcases x with ⟨p, b⟩
    cases b
    · apply Prod.ext
      · simp [xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip,
          e.2 (p, false)]
      · simp [xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip]
    · have hsecond_ne : (e.1 (p, true)).2 ≠ (e.1 (p, false)).2 := by
        intro hsecond
        have himage : e.1 (p, true) = e.1 (p, false) := by
          apply Prod.ext
          · simp [e.2 (p, true), e.2 (p, false)]
          · exact hsecond
        have hpreimage : (p, true) = (p, false) := e.1.injective himage
        cases hpreimage
      have hsecond : Bool.not (e.1 (p, false)).2 = (e.1 (p, true)).2 := by
        cases hfalse : (e.1 (p, false)).2 <;> cases htrue : (e.1 (p, true)).2 <;>
          simp [hfalse, htrue] at hsecond_ne ⊢
      apply Prod.ext
      · simpa using (e.2 (p, true)).symm
      · simp [xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip,
          hsecond]
  right_inv := by
    intro s
    funext p
    by_cases hp : s p <;>
      simp [xi_integer_ellipse_area_preserving_automorphism_product_blockwise_bool_flip, hp]

/-- Concrete product decomposition of area-preserving atom automorphisms into primewise flips. -/
def xi_integer_ellipse_area_preserving_automorphism_product_statement : Prop :=
  xi_integer_ellipse_free_commutative_monoid_statement ∧
    Nonempty
      (xi_integer_ellipse_area_preserving_automorphism_product_area_preserving_atom_perm ≃
        (Omega.Conclusion.PrimeRegisterVector → Bool))

/-- Paper label: `cor:xi-integer-ellipse-area-preserving-automorphism-product`. -/
theorem paper_xi_integer_ellipse_area_preserving_automorphism_product :
    xi_integer_ellipse_area_preserving_automorphism_product_statement := by
  exact ⟨paper_xi_integer_ellipse_free_commutative_monoid,
    ⟨xi_integer_ellipse_area_preserving_automorphism_product_atom_perm_equiv⟩⟩

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Zeta

abbrev xi_window6_boundary_center_nonintrinsic_orbit_center := Fin 8 → ZMod 2

def xi_window6_boundary_center_nonintrinsic_orbit_boundary
    (x : xi_window6_boundary_center_nonintrinsic_orbit_center) : Prop :=
  ∀ i : Fin 8, 3 ≤ i.val → x i = 0

def xi_window6_boundary_center_nonintrinsic_orbit_shifted
    (x : xi_window6_boundary_center_nonintrinsic_orbit_center) : Prop :=
  ∀ i : Fin 8, i.val < 5 → x i = 0

def xi_window6_boundary_center_nonintrinsic_orbit_boundaryPoint
    (u : Fin 3 → ZMod 2) : xi_window6_boundary_center_nonintrinsic_orbit_center :=
  fun i => if h : i.val < 3 then u ⟨i.val, h⟩ else 0

def xi_window6_boundary_center_nonintrinsic_orbit_boundaryEquiv :
    {x : xi_window6_boundary_center_nonintrinsic_orbit_center //
        xi_window6_boundary_center_nonintrinsic_orbit_boundary x} ≃ (Fin 3 → ZMod 2) where
  toFun x := fun i => x.1 ⟨i.val, by omega⟩
  invFun u :=
    ⟨xi_window6_boundary_center_nonintrinsic_orbit_boundaryPoint u, by
      intro i hi
      simp [xi_window6_boundary_center_nonintrinsic_orbit_boundaryPoint, not_lt.mpr hi]⟩
  left_inv x := by
    ext i
    by_cases hi : i.val < 3
    · simp [xi_window6_boundary_center_nonintrinsic_orbit_boundaryPoint, hi]
    · have hzero : x.1 i = 0 := x.2 i (not_lt.mp hi)
      simp [xi_window6_boundary_center_nonintrinsic_orbit_boundaryPoint, hi, hzero]
  right_inv u := by
    ext i
    simp [xi_window6_boundary_center_nonintrinsic_orbit_boundaryPoint]

def xi_window6_boundary_center_nonintrinsic_orbit_perm (i : Fin 8) : Fin 8 :=
  match i with
  | 0 => 5
  | 1 => 6
  | 2 => 7
  | 3 => 3
  | 4 => 4
  | 5 => 0
  | 6 => 1
  | 7 => 2

lemma xi_window6_boundary_center_nonintrinsic_orbit_perm_involutive (i : Fin 8) :
    xi_window6_boundary_center_nonintrinsic_orbit_perm
        (xi_window6_boundary_center_nonintrinsic_orbit_perm i) = i := by
  fin_cases i <;> rfl

def xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv :
    xi_window6_boundary_center_nonintrinsic_orbit_center ≃ₗ[ZMod 2]
      xi_window6_boundary_center_nonintrinsic_orbit_center where
  toFun x := fun i => x (xi_window6_boundary_center_nonintrinsic_orbit_perm i)
  invFun x := fun i => x (xi_window6_boundary_center_nonintrinsic_orbit_perm i)
  map_add' x y := by
    ext i
    rfl
  map_smul' c x := by
    ext i
    rfl
  left_inv x := by
    ext i
    simp [xi_window6_boundary_center_nonintrinsic_orbit_perm_involutive]
  right_inv x := by
    ext i
    simp [xi_window6_boundary_center_nonintrinsic_orbit_perm_involutive]

lemma xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv_maps_boundary
    (x : xi_window6_boundary_center_nonintrinsic_orbit_center)
    (hx : xi_window6_boundary_center_nonintrinsic_orbit_boundary x) :
    xi_window6_boundary_center_nonintrinsic_orbit_shifted
      (xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv x) := by
  intro i hi
  fin_cases i
  · simpa [xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv,
      xi_window6_boundary_center_nonintrinsic_orbit_perm] using hx 5 (by norm_num)
  · simpa [xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv,
      xi_window6_boundary_center_nonintrinsic_orbit_perm] using hx 6 (by norm_num)
  · simpa [xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv,
      xi_window6_boundary_center_nonintrinsic_orbit_perm] using hx 7 (by norm_num)
  · simpa [xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv,
      xi_window6_boundary_center_nonintrinsic_orbit_perm] using hx 3 (by norm_num)
  · simpa [xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv,
      xi_window6_boundary_center_nonintrinsic_orbit_perm] using hx 4 (by norm_num)
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

lemma xi_window6_boundary_center_nonintrinsic_orbit_boundary_ne_shifted :
    {x : xi_window6_boundary_center_nonintrinsic_orbit_center |
        xi_window6_boundary_center_nonintrinsic_orbit_boundary x} ≠
      {x : xi_window6_boundary_center_nonintrinsic_orbit_center |
        xi_window6_boundary_center_nonintrinsic_orbit_shifted x} := by
  intro h
  let e0 : xi_window6_boundary_center_nonintrinsic_orbit_center :=
    fun i => if i = (0 : Fin 8) then 1 else 0
  have hboundary : xi_window6_boundary_center_nonintrinsic_orbit_boundary e0 := by
    intro i hi
    have hne : i ≠ (0 : Fin 8) := by
      intro h0
      have : i.val = 0 := congrArg Fin.val h0
      omega
    simp [e0, hne]
  have hshifted : xi_window6_boundary_center_nonintrinsic_orbit_shifted e0 := by
    exact Set.ext_iff.mp h e0 |>.mp hboundary
  have hzero := hshifted 0 (by norm_num)
  norm_num [e0] at hzero

def xi_window6_boundary_center_nonintrinsic_orbit_gaussianCount : ℕ :=
  ((2 ^ 8 - 1) * (2 ^ 8 - 2) * (2 ^ 8 - 4)) /
    ((2 ^ 3 - 1) * (2 ^ 3 - 2) * (2 ^ 3 - 4))

def xi_window6_boundary_center_nonintrinsic_orbit_statement : Prop :=
  Fintype.card xi_window6_boundary_center_nonintrinsic_orbit_center = 2 ^ 8 ∧
    Nonempty
      ({x : xi_window6_boundary_center_nonintrinsic_orbit_center //
          xi_window6_boundary_center_nonintrinsic_orbit_boundary x} ≃ (Fin 3 → ZMod 2)) ∧
    Fintype.card (Fin 3 → ZMod 2) = 2 ^ 3 ∧
    (∀ x, xi_window6_boundary_center_nonintrinsic_orbit_boundary x →
      xi_window6_boundary_center_nonintrinsic_orbit_shifted
        (xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv x)) ∧
    {x : xi_window6_boundary_center_nonintrinsic_orbit_center |
        xi_window6_boundary_center_nonintrinsic_orbit_boundary x} ≠
      {x : xi_window6_boundary_center_nonintrinsic_orbit_center |
        xi_window6_boundary_center_nonintrinsic_orbit_shifted x} ∧
    xi_window6_boundary_center_nonintrinsic_orbit_gaussianCount = 97155

/-- Paper label: `thm:xi-window6-boundary-center-nonintrinsic-orbit`. -/
theorem paper_xi_window6_boundary_center_nonintrinsic_orbit :
    xi_window6_boundary_center_nonintrinsic_orbit_statement := by
  refine ⟨?_, ⟨xi_window6_boundary_center_nonintrinsic_orbit_boundaryEquiv⟩, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_window6_boundary_center_nonintrinsic_orbit_center]
  · norm_num
  · exact xi_window6_boundary_center_nonintrinsic_orbit_linearEquiv_maps_boundary
  · exact xi_window6_boundary_center_nonintrinsic_orbit_boundary_ne_shifted
  · native_decide

end Omega.Zeta

import Mathlib.Tactic
import Omega.Zeta.XiTimePart9gHolographicPrefixIsometryOnLine

namespace Omega.Zeta

open Omega.Conclusion

/-- Compact data for the binary hologram model underlying the self-affine Cantor dynamics. The
condition `slice = 1` forces the canonical alphabet to be exactly `{0,1}`. -/
structure xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data where
  xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice : CanonicalSliceData
  xi_time_part62dc_hologram_selfaffine_cantor_dynamics_binary :
    xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice = 1

/-- Left binary branch digit. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    Fin (D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice.M + 1) :=
  ⟨0, by simp [Omega.Conclusion.CanonicalSliceData.M,
    D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_binary]⟩

/-- Right binary branch digit. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_digit
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    Fin (D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice.M + 1) :=
  ⟨1, by simp [Omega.Conclusion.CanonicalSliceData.M,
    D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_binary]⟩

/-- Left one-step prefix. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_prefix
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice.fixedPointsAtLayer 1 :=
  fun _ => xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit D

/-- Right one-step prefix. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_prefix
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice.fixedPointsAtLayer 1 :=
  fun _ => xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_digit D

/-- Left branch cylinder in the digit-stream model. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_cylinder
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    Set (CanonicalDigitStream D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice) :=
  xi_time_part9g_holographic_prefix_isometry_on_line_cylinder
    D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
    1
    (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_prefix D)

/-- Right branch cylinder in the digit-stream model. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_cylinder
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    Set (CanonicalDigitStream D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice) :=
  xi_time_part9g_holographic_prefix_isometry_on_line_cylinder
    D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
    1
    (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_prefix D)

/-- Left branch piece on the coded hologram image. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_branch_piece
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    Set (CanonicalFixedpointCode D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice) :=
  {c | c 0 = xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit D}

/-- Right branch piece on the coded hologram image. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_branch_piece
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    Set (CanonicalFixedpointCode D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice) :=
  {c | c 0 = xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_digit D}

/-- Global hologram dynamics: the transported left shift. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_global_map
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    CanonicalFixedpointCode D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice →
      CanonicalFixedpointCode D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice :=
  canonicalCodeShift D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice

/-- Left branch inverse obtained by prepending the left digit. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_inverse
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    CanonicalFixedpointCode D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice →
      CanonicalFixedpointCode D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
  | _c, 0 => xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit D
  | c, n + 1 => c n

/-- Right branch inverse obtained by prepending the right digit. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_inverse
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    CanonicalFixedpointCode D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice →
      CanonicalFixedpointCode D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
  | _c, 0 => xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_digit D
  | c, n + 1 => c n

/-- Witness stream used to invoke the existing prefix/cylinder package at depth `1`. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_a
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    CanonicalDigitStream D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice :=
  fun _ => xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit D

/-- Companion witness stream: same first digit, different second digit. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_b
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    CanonicalDigitStream D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
  | 0 => xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit D
  | _ + 1 => xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_digit D

private lemma xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_right_ne
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit D ≠
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_digit D := by
  intro h
  have : (0 : Fin 2) = 1 := by
    simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit,
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_digit,
      Omega.Conclusion.CanonicalSliceData.M] using h
  norm_num at this

private lemma xi_time_part62dc_hologram_selfaffine_cantor_dynamics_first_difference_at_one
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    xi_time_part9g_holographic_prefix_isometry_on_line_firstDifferenceAt
      D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
      1
      (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_a D)
      (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_b D) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    have ht0 : t = 0 := by omega
    subst ht0
    simp [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_a,
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_b]
  · simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_a,
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_b] using
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_right_ne D

private lemma xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_branch_piece_eq_coset
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_branch_piece D =
      xi_time_part9g_holographic_prefix_isometry_on_line_coset
        D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
        1
        (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_prefix D) := by
  ext c
  constructor
  · intro hc
    funext i
    fin_cases i
    simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_prefix] using hc
  · intro hc
    simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_prefix] using
      congrFun hc ⟨0, by decide⟩

private lemma xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_branch_piece_eq_coset
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_branch_piece D =
      xi_time_part9g_holographic_prefix_isometry_on_line_coset
        D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
        1
        (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_prefix D) := by
  ext c
  constructor
  · intro hc
    funext i
    fin_cases i
    simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_prefix] using hc
  · intro hc
    simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_prefix] using
      congrFun hc ⟨0, by decide⟩

private lemma xi_time_part62dc_hologram_selfaffine_cantor_dynamics_one_prefix_cylinder_image
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    ∀ w : D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice.fixedPointsAtLayer 1,
      Set.image
          (xi_time_part9g_holographic_prefix_isometry_on_line_address
            D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice)
          (xi_time_part9g_holographic_prefix_isometry_on_line_cylinder
            D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
            1
            w) =
        xi_time_part9g_holographic_prefix_isometry_on_line_coset
          D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
          1
          w := by
  have hprefix :=
    paper_xi_time_part9g_holographic_prefix_isometry_on_line
      D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
      1
      (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_a D)
      (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_witness_stream_b D)
      (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_first_difference_at_one D)
  exact hprefix.2.2

/-- The binary branch pieces are disjoint, cover the hologram image, arise as the images of the
corresponding prefix cylinders, and the global shift map is inverted on each branch by the
appropriate prepend map. -/
def xi_time_part62dc_hologram_selfaffine_cantor_dynamics_statement
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) : Prop :=
  Function.Bijective
      (xi_time_part9g_holographic_prefix_isometry_on_line_address
        D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice) ∧
    Disjoint
      (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_branch_piece D)
      (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_branch_piece D) ∧
    Set.range
        (xi_time_part9g_holographic_prefix_isometry_on_line_address
          D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice) =
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_branch_piece D ∪
        xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_branch_piece D ∧
    Set.image
        (xi_time_part9g_holographic_prefix_isometry_on_line_address
          D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice)
        (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_cylinder D) =
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_branch_piece D ∧
    Set.image
        (xi_time_part9g_holographic_prefix_isometry_on_line_address
          D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice)
        (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_cylinder D) =
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_branch_piece D ∧
    (∀ c,
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_global_map D
          (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_inverse D c) =
        c) ∧
    (∀ c,
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_global_map D
          (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_inverse D c) =
        c) ∧
    (∀ c,
      c ∈ xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_branch_piece D →
        xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_inverse D
            (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_global_map D c) =
          c) ∧
    ∀ c,
      c ∈ xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_branch_piece D →
        xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_inverse D
            (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_global_map D c) =
          c

/-- Paper label: `thm:xi-time-part62dc-hologram-selfaffine-cantor-dynamics`. In the binary
canonical hologram model, the address image splits into the two first-digit branch pieces, the
existing prefix/cylinder conjugacy identifies those pieces with the corresponding cylinders, and
the transported shift is inverted on each branch by prepending the branch digit. -/
theorem paper_xi_time_part62dc_hologram_selfaffine_cantor_dynamics
    (D : xi_time_part62dc_hologram_selfaffine_cantor_dynamics_data) :
    xi_time_part62dc_hologram_selfaffine_cantor_dynamics_statement D := by
  rcases paper_conclusion_canonical_fixedpoint_fullshift_conjugacy
      D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice with
    ⟨_, _, hbij, _, _, _⟩
  refine ⟨hbij, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Set.disjoint_left.2 ?_
    intro c hcLeft hcRight
    exact
      xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_right_ne D
        (hcLeft.symm.trans hcRight)
  · ext c
    constructor
    · rintro ⟨a, rfl⟩
      have hcases :
          a 0 = xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit D ∨
            a 0 = xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_digit D := by
        have hlt : (a 0).val < 2 := by
          simpa [Omega.Conclusion.CanonicalSliceData.M,
            D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_binary] using (a 0).isLt
        have hval : (a 0).val = 0 ∨ (a 0).val = 1 := by omega
        rcases hval with hzero | hone
        · left
          apply Fin.ext
          simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_digit,
            Omega.Conclusion.CanonicalSliceData.M,
            D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_binary] using hzero
        · right
          apply Fin.ext
          simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_digit,
            Omega.Conclusion.CanonicalSliceData.M,
            D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_binary] using hone
      rcases hcases with hLeft | hRight
      · exact Or.inl hLeft
      · exact Or.inr hRight
    · intro hc
      exact ⟨c, rfl⟩
  · calc
      Set.image
          (xi_time_part9g_holographic_prefix_isometry_on_line_address
            D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice)
          (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_cylinder D) =
        xi_time_part9g_holographic_prefix_isometry_on_line_coset
          D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
          1
          (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_prefix D) := by
            simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_cylinder] using
              xi_time_part62dc_hologram_selfaffine_cantor_dynamics_one_prefix_cylinder_image D
                (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_prefix D)
      _ = xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_branch_piece D := by
            rw [← xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_branch_piece_eq_coset D]
  · calc
      Set.image
          (xi_time_part9g_holographic_prefix_isometry_on_line_address
            D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice)
          (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_cylinder D) =
        xi_time_part9g_holographic_prefix_isometry_on_line_coset
          D.xi_time_part62dc_hologram_selfaffine_cantor_dynamics_slice
          1
          (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_prefix D) := by
            simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_cylinder] using
              xi_time_part62dc_hologram_selfaffine_cantor_dynamics_one_prefix_cylinder_image D
                (xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_prefix D)
      _ = xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_branch_piece D := by
            rw [← xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_branch_piece_eq_coset D]
  · intro c
    funext n
    rfl
  · intro c
    funext n
    rfl
  · intro c hc
    funext n
    cases n with
    | zero =>
        simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_left_inverse,
          xi_time_part62dc_hologram_selfaffine_cantor_dynamics_global_map] using hc.symm
    | succ n =>
        rfl
  · intro c hc
    funext n
    cases n with
    | zero =>
        simpa [xi_time_part62dc_hologram_selfaffine_cantor_dynamics_right_inverse,
          xi_time_part62dc_hologram_selfaffine_cantor_dynamics_global_map] using hc.symm
    | succ n =>
        rfl

end Omega.Zeta

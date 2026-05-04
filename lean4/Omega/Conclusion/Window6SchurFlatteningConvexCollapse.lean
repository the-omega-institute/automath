import Mathlib.Tactic

namespace Omega.Conclusion

/-- Ordinary window-`6` sorted fiber sizes from the histogram `1:2, 2:4, 3:8, 4:5, 5:2`. -/
def conclusion_window6_schur_flattening_convex_collapse_ord_fibers : List ℕ :=
  [5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 1, 1]

/-- Binary-uplift window-`6` sorted fiber sizes from the histogram `2:8, 3:4, 4:9`. -/
def conclusion_window6_schur_flattening_convex_collapse_bin_fibers : List ℕ :=
  [4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]

/-- Prefix sum of the first `k` entries. -/
def conclusion_window6_schur_flattening_convex_collapse_prefix_sum
    (d : List ℕ) (k : ℕ) : ℕ :=
  (d.take k).sum

/-- The normalized probability vector attached to a sorted fiber list. -/
def conclusion_window6_schur_flattening_convex_collapse_normalize (d : List ℕ) :
    List ℚ :=
  d.map (fun n => (n : ℚ) / 64)

/-- Ordinary normalized window-`6` vector. -/
def conclusion_window6_schur_flattening_convex_collapse_p_ord : List ℚ :=
  conclusion_window6_schur_flattening_convex_collapse_normalize
    conclusion_window6_schur_flattening_convex_collapse_ord_fibers

/-- Binary-uplift normalized window-`6` vector. -/
def conclusion_window6_schur_flattening_convex_collapse_p_bin : List ℚ :=
  conclusion_window6_schur_flattening_convex_collapse_normalize
    conclusion_window6_schur_flattening_convex_collapse_bin_fibers

/-- Concrete finite strict majorization certificate for equally sized integer vectors. -/
def conclusion_window6_schur_flattening_convex_collapse_strict_majorizes
    (x y : List ℕ) : Prop :=
  x.length = y.length ∧
    x.sum = y.sum ∧
    (List.range (x.length + 1)).map
        (fun k =>
          decide
            (conclusion_window6_schur_flattening_convex_collapse_prefix_sum y k ≤
              conclusion_window6_schur_flattening_convex_collapse_prefix_sum x k)) =
      List.replicate (x.length + 1) true ∧
    conclusion_window6_schur_flattening_convex_collapse_prefix_sum y 1 <
      conclusion_window6_schur_flattening_convex_collapse_prefix_sum x 1

/-- Boolean upper-bound certificate used to keep the max check finite. -/
def conclusion_window6_schur_flattening_convex_collapse_le_all (d : List ℚ) (M : ℚ) :
    Prop :=
  (d.map (fun q => decide (q ≤ M))).all id = true

/-- Boolean membership certificate for rational lists. -/
def conclusion_window6_schur_flattening_convex_collapse_contains (d : List ℚ) (M : ℚ) :
    Prop :=
  (d.map (fun q => decide (q = M))).any id = true

/-- A finite certificate that `M` is the maximum displayed entry of `d`. -/
def conclusion_window6_schur_flattening_convex_collapse_normalized_max
    (d : List ℚ) (M : ℚ) : Prop :=
  conclusion_window6_schur_flattening_convex_collapse_contains d M ∧
    conclusion_window6_schur_flattening_convex_collapse_le_all d M

/-- The normalized square sum, i.e. the collision energy of the vector. -/
def conclusion_window6_schur_flattening_convex_collapse_square_sum (d : List ℚ) : ℚ :=
  (d.map (fun q => q * q)).sum

/-- Concrete statement for `thm:conclusion-window6-schur-flattening-convex-collapse`. -/
def conclusion_window6_schur_flattening_convex_collapse_statement : Prop :=
  conclusion_window6_schur_flattening_convex_collapse_ord_fibers.length = 21 ∧
    conclusion_window6_schur_flattening_convex_collapse_bin_fibers.length = 21 ∧
    conclusion_window6_schur_flattening_convex_collapse_ord_fibers.sum = 64 ∧
    conclusion_window6_schur_flattening_convex_collapse_bin_fibers.sum = 64 ∧
    conclusion_window6_schur_flattening_convex_collapse_strict_majorizes
      conclusion_window6_schur_flattening_convex_collapse_ord_fibers
      conclusion_window6_schur_flattening_convex_collapse_bin_fibers ∧
    (List.range 22).map
        (conclusion_window6_schur_flattening_convex_collapse_prefix_sum
          conclusion_window6_schur_flattening_convex_collapse_ord_fibers) =
      [0, 5, 10, 14, 18, 22, 26, 30, 33, 36, 39, 42, 45, 48, 51, 54, 56, 58,
        60, 62, 63, 64] ∧
    (List.range 22).map
        (conclusion_window6_schur_flattening_convex_collapse_prefix_sum
          conclusion_window6_schur_flattening_convex_collapse_bin_fibers) =
      [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 39, 42, 45, 48, 50, 52, 54, 56,
        58, 60, 62, 64] ∧
    conclusion_window6_schur_flattening_convex_collapse_normalized_max
      conclusion_window6_schur_flattening_convex_collapse_p_bin ((4 : ℚ) / 64) ∧
    conclusion_window6_schur_flattening_convex_collapse_normalized_max
      conclusion_window6_schur_flattening_convex_collapse_p_ord ((5 : ℚ) / 64) ∧
    ((4 : ℚ) / 64) < ((5 : ℚ) / 64) ∧
    conclusion_window6_schur_flattening_convex_collapse_square_sum
        conclusion_window6_schur_flattening_convex_collapse_p_bin =
      (212 : ℚ) / (64 ^ 2) ∧
    conclusion_window6_schur_flattening_convex_collapse_square_sum
        conclusion_window6_schur_flattening_convex_collapse_p_ord =
      (220 : ℚ) / (64 ^ 2) ∧
    ((212 : ℚ) / (64 ^ 2)) < ((220 : ℚ) / (64 ^ 2)) ∧
    (∀ Φ : List ℚ → ℚ,
      (conclusion_window6_schur_flattening_convex_collapse_strict_majorizes
          conclusion_window6_schur_flattening_convex_collapse_ord_fibers
          conclusion_window6_schur_flattening_convex_collapse_bin_fibers →
          Φ conclusion_window6_schur_flattening_convex_collapse_p_bin ≤
            Φ conclusion_window6_schur_flattening_convex_collapse_p_ord) →
      Φ conclusion_window6_schur_flattening_convex_collapse_p_bin ≤
        Φ conclusion_window6_schur_flattening_convex_collapse_p_ord) ∧
    (∀ H : List ℚ → ℚ,
      (conclusion_window6_schur_flattening_convex_collapse_strict_majorizes
          conclusion_window6_schur_flattening_convex_collapse_ord_fibers
          conclusion_window6_schur_flattening_convex_collapse_bin_fibers →
          H conclusion_window6_schur_flattening_convex_collapse_p_bin >
            H conclusion_window6_schur_flattening_convex_collapse_p_ord) →
      H conclusion_window6_schur_flattening_convex_collapse_p_bin >
        H conclusion_window6_schur_flattening_convex_collapse_p_ord)

/-- Paper label: `thm:conclusion-window6-schur-flattening-convex-collapse`. -/
theorem paper_conclusion_window6_schur_flattening_convex_collapse :
    conclusion_window6_schur_flattening_convex_collapse_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · unfold conclusion_window6_schur_flattening_convex_collapse_strict_majorizes
    native_decide
  · native_decide
  · native_decide
  · unfold conclusion_window6_schur_flattening_convex_collapse_normalized_max
    unfold conclusion_window6_schur_flattening_convex_collapse_contains
    unfold conclusion_window6_schur_flattening_convex_collapse_le_all
    unfold conclusion_window6_schur_flattening_convex_collapse_p_bin
    unfold conclusion_window6_schur_flattening_convex_collapse_normalize
    unfold conclusion_window6_schur_flattening_convex_collapse_bin_fibers
    native_decide
  · unfold conclusion_window6_schur_flattening_convex_collapse_normalized_max
    unfold conclusion_window6_schur_flattening_convex_collapse_contains
    unfold conclusion_window6_schur_flattening_convex_collapse_le_all
    unfold conclusion_window6_schur_flattening_convex_collapse_p_ord
    unfold conclusion_window6_schur_flattening_convex_collapse_normalize
    unfold conclusion_window6_schur_flattening_convex_collapse_ord_fibers
    native_decide
  · norm_num
  · native_decide
  · native_decide
  · norm_num
  · intro Φ hΦ
    exact hΦ (by
      unfold conclusion_window6_schur_flattening_convex_collapse_strict_majorizes
      native_decide)
  · intro H hH
    exact hH (by
      unfold conclusion_window6_schur_flattening_convex_collapse_strict_majorizes
      native_decide)

end Omega.Conclusion

import Mathlib.Tactic
import Omega.Folding.FoldZeroCosetV2IntersectionRigidity

namespace Omega.Folding

/-- The rigid gcd-coset that models the pairwise zero-coset intersection once the common
congruence data has been reduced to the gcd layer. -/
abbrev fold_zero_coset_intersection_gcd_coset (M g h : ℕ) : Finset ℕ :=
  foldZeroOddCoset M (Nat.gcd g h)

private lemma fold_zero_coset_intersection_gcd_coset_card
    (M d : ℕ) (hM : Even M) (hMpos : 0 < M) (hd : d ∣ M / 2) (hdpos : 0 < d) :
    (foldZeroOddCoset M d).card = d := by
  rcases hM with ⟨m, rfl⟩
  have hmpos : 0 < m := by omega
  have hhalfm : (m + m) / 2 = m := by omega
  have hd' : d ∣ m := by simpa [hhalfm] using hd
  rcases hd' with ⟨q, rfl⟩
  have hqpos : 0 < q := by
    have hqne : q ≠ 0 := by
      intro hq
      subst hq
      omega
    exact Nat.pos_of_ne_zero hqne
  have hquot : ((d * q + d * q) / 2) / d = q := by
    have hsum : d * q + d * q = 2 * (d * q) := by rw [two_mul]
    rw [hsum]
    simp [hdpos.ne']
  unfold foldZeroOddCoset
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    have hab' : q * (2 * a + 1) = q * (2 * b + 1) := by
      simpa [hquot] using hab
    have hab'' : 2 * a + 1 = 2 * b + 1 := Nat.eq_of_mul_eq_mul_left hqpos hab'
    omega

/-- Paper label: `lem:fold-zero-coset-intersection`.
The existing rigid odd-coset package already identifies the gcd layer that governs pairwise
intersections of fold zero cosets. Under the standard even-modulus hypotheses, that gcd layer is
admissible for `M / 2`, and its rigid odd-coset model has exactly `gcd(g,h)` elements. -/
theorem paper_fold_zero_coset_intersection (M g h : ℕ)
    (hM : Even M) (hMpos : 0 < M) (hg : g ∣ M / 2) (hh : h ∣ M / 2)
    (_hgpos : 0 < g) (hhpos : 0 < h) :
    FoldZeroCosetV2IntersectionSpec M g h ∧
      (fold_zero_coset_intersection_gcd_coset M g h).card = Nat.gcd g h := by
  have hSpec := paper_xi_fold_zero_coset_v2_intersection_rigidity M g h hM hg hh
  have hdpos : 0 < Nat.gcd g h := Nat.gcd_pos_of_pos_right g hhpos
  refine ⟨hSpec, ?_⟩
  exact fold_zero_coset_intersection_gcd_coset_card M (Nat.gcd g h) hM hMpos hSpec.1 hdpos

end Omega.Folding

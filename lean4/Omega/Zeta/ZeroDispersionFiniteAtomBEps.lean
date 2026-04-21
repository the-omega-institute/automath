import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The finite-atom zero-dispersion success curve `Ψ(c) = E[min(1, exp(c) / Z)]`. -/
noncomputable def finiteAtomPsi {n : ℕ} (z p : Fin (n + 1) → ℝ) (c : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), p i * min 1 (Real.exp c / z i)

/-- The cumulative mass of the atoms up to index `j`. -/
noncomputable def finiteAtomPrefixMass {n : ℕ} (p : Fin (n + 1) → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), if i.1 ≤ j then p i else 0

/-- The weighted tail slope beyond index `j`. -/
noncomputable def finiteAtomTailSlope {n : ℕ} (z p : Fin (n + 1) → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), if j < i.1 then p i / z i else 0

/-- The affine-in-`exp(c)` candidate inverse on the `j`-th interval. -/
noncomputable def finiteAtomCandidateB {n : ℕ} (z p : Fin (n + 1) → ℝ) (j : ℕ) (ε : ℝ) : ℝ :=
  Real.log ((1 - ε - finiteAtomPrefixMass p j) / finiteAtomTailSlope z p j)

private lemma finiteAtomPsi_eq_split {n : ℕ} (z p : Fin (n + 1) → ℝ) (j : ℕ) (c : ℝ)
    (hz_pos : ∀ i, 0 < z i)
    (hsat : ∀ i, i.1 ≤ j → z i ≤ Real.exp c)
    (hunsat : ∀ i, j < i.1 → Real.exp c < z i) :
    finiteAtomPsi z p c = finiteAtomPrefixMass p j + Real.exp c * finiteAtomTailSlope z p j := by
  calc
    finiteAtomPsi z p c =
        ∑ i : Fin (n + 1),
          ((if i.1 ≤ j then p i else 0) + Real.exp c * (if j < i.1 then p i / z i else 0)) := by
          unfold finiteAtomPsi
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hij : i.1 ≤ j
          · have hratio : 1 ≤ Real.exp c / z i := by
              exact (one_le_div₀ (hz_pos i)).2 (hsat i hij)
            simp [hij, min_eq_left hratio]
          · have hij' : j < i.1 := lt_of_not_ge hij
            have hratio : Real.exp c / z i ≤ 1 := by
              rw [div_le_iff₀ (hz_pos i)]
              simpa using le_of_lt (hunsat i hij')
            have hmul :
                p i * (Real.exp c / z i) = Real.exp c * (p i / z i) := by
              field_simp [(hz_pos i).ne']
            simp [hij, min_eq_right hratio, hmul]
    _ = finiteAtomPrefixMass p j + Real.exp c * finiteAtomTailSlope z p j := by
          unfold finiteAtomPrefixMass finiteAtomTailSlope
          rw [Finset.sum_add_distrib, Finset.mul_sum]

private lemma finiteAtomPsi_eq_one_at_top {n : ℕ} (z p : Fin (n + 1) → ℝ)
    (hz_pos : ∀ i, 0 < z i) (hp_sum : ∑ i : Fin (n + 1), p i = 1)
    (hTop : ∀ i, z i ≤ z ⟨n, Nat.lt_succ_self n⟩) :
    finiteAtomPsi z p (Real.log (z ⟨n, Nat.lt_succ_self n⟩)) = 1 := by
  unfold finiteAtomPsi
  have hsum :
      ∀ i : Fin (n + 1),
        p i * min 1 (Real.exp (Real.log (z ⟨n, Nat.lt_succ_self n⟩)) / z i) = p i := by
    intro i
    have hratio : 1 ≤ Real.exp (Real.log (z ⟨n, Nat.lt_succ_self n⟩)) / z i := by
      have hzmax_pos : 0 < z ⟨n, Nat.lt_succ_self n⟩ := hz_pos ⟨n, Nat.lt_succ_self n⟩
      rw [Real.exp_log hzmax_pos]
      exact (one_le_div₀ (hz_pos i)).2 (hTop i)
    rw [min_eq_left hratio, mul_one]
  calc
    finiteAtomPsi z p (Real.log (z ⟨n, Nat.lt_succ_self n⟩)) =
      ∑ i : Fin (n + 1), p i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact hsum i
    _ = 1 := hp_sum

/-- Paper label: `thm:xi-zero-dispersion-finite-atom-b-eps`.
For a finite atomic law, once a candidate `b(ε)` lies on a fixed affine branch of `Ψ`, evaluating
`Ψ` at that candidate recovers `1 - ε`; at `ε = 0`, the top atom gives the endpoint `b(0)`. -/
theorem paper_xi_zero_dispersion_finite_atom_b_eps
    (n : ℕ) (z p : Fin (n + 1) → ℝ) (j : ℕ) (_hj : j < n) (ε : ℝ)
    (hz_pos : ∀ i, 0 < z i)
    (hp_sum : ∑ i : Fin (n + 1), p i = 1)
    (hgap : finiteAtomPrefixMass p j < 1 - ε)
    (hQpos : 0 < finiteAtomTailSlope z p j)
    (hCandSat : ∀ i, i.1 ≤ j → z i ≤ Real.exp (finiteAtomCandidateB z p j ε))
    (hCandUnsat : ∀ i, j < i.1 → Real.exp (finiteAtomCandidateB z p j ε) < z i)
    (hTop : ∀ i, z i ≤ z ⟨n, Nat.lt_succ_self n⟩) :
    finiteAtomPsi z p (finiteAtomCandidateB z p j ε) = 1 - ε ∧
      finiteAtomPsi z p (Real.log (z ⟨n, Nat.lt_succ_self n⟩)) = 1 := by
  let P := finiteAtomPrefixMass p j
  let Q := finiteAtomTailSlope z p j
  let b := finiteAtomCandidateB z p j ε
  have hb_split :
      finiteAtomPsi z p b = P + Real.exp b * Q := by
    simpa [P, Q, b] using finiteAtomPsi_eq_split z p j b hz_pos hCandSat hCandUnsat
  have hnum_pos : 0 < 1 - ε - P := by
    linarith
  have harg_pos : 0 < (1 - ε - P) / Q := div_pos hnum_pos hQpos
  have hb_exp : Real.exp b = (1 - ε - P) / Q := by
    unfold b finiteAtomCandidateB
    simp [P, Q, Real.exp_log harg_pos]
  have hb_value : finiteAtomPsi z p b = 1 - ε := by
    calc
      finiteAtomPsi z p b = P + Real.exp b * Q := hb_split
      _ = P + ((1 - ε - P) / Q) * Q := by rw [hb_exp]
      _ = P + (1 - ε - P) := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hQpos.ne', mul_one]
      _ = 1 - ε := by
        ring
  have htop_value :
      finiteAtomPsi z p (Real.log (z ⟨n, Nat.lt_succ_self n⟩)) = 1 :=
    finiteAtomPsi_eq_one_at_top z p hz_pos hp_sum hTop
  exact ⟨by simpa [b] using hb_value, htop_value⟩

end Omega.Zeta

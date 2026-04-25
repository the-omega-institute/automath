import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Conclusion.TqftGenusHausdorffMomentSequence

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `prop:conclusion-tqft-genus-logconvexity`. For the normalized genus partition
sequence attached to the concrete fiber multiplicities, the midpoint log-convexity inequality
`Z₁² ≤ Z₀ Z₂` is the finite Cauchy-Schwarz inequality for the node list `d_m(x)⁻²`. -/
theorem paper_conclusion_tqft_genus_logconvexity
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) :
    let Z := D.conclusion_tqft_genus_hausdorff_moment_sequence_partition
    Z 1 ^ 2 ≤ Z 0 * Z 2 := by
  dsimp
  let a : Fin D.n → ℝ := fun x => D.conclusion_tqft_genus_hausdorff_moment_sequence_node x
  let s : ℝ := ∑ x : Fin D.n, a x
  let t : ℝ := ∑ x : Fin D.n, a x ^ 2
  have hn_pos : (0 : ℝ) < D.n := by
    exact_mod_cast D.conclusion_tqft_genus_hausdorff_moment_sequence_nonempty
  have hn_ne : (D.n : ℝ) ≠ 0 := by
    positivity
  have hsq :
      s ^ 2 ≤ (D.n : ℝ) * t := by
    simpa [a, s, t] using
      (Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (s := Finset.univ)
        (fun _ : Fin D.n => (1 : ℝ)) a)
  have hineq : s * s / (D.n * D.n) ≤ t / D.n := by
    field_simp [hn_ne]
    nlinarith [hsq]
  simpa [conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_partition,
    a, s, t, pow_two, hn_ne, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hineq

/-- Core normalized genus partition function for the concrete nonintegral-average wrapper. -/
noncomputable def conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition_core
    (n : ℕ) (dm : Fin n → ℕ) (g : ℕ) : ℝ :=
  (∑ x : Fin n, (1 / (dm x : ℝ) ^ 2) ^ g) / (n : ℝ)

/-- Concrete data for the nonintegral-average strict genus-logconvexity criterion. The two
logical proof fields are the already-established weak logconvexity and its equality-rigidity
criterion, specialized to the concrete finite multiplicity profile in this wrapper. -/
structure conclusion_tqft_genus_strict_logconvexity_nonintegral_average_Data where
  m : ℕ
  n : ℕ
  dm : Fin n → ℕ
  dm_pos : ∀ x, 1 ≤ dm x
  nonempty : 0 < n
  totalMultiplicity : (∑ x : Fin n, dm x) = 2 ^ m
  nonintegralAverage : ¬ ∃ d : ℕ, 1 ≤ d ∧ ((2 : ℝ) ^ m) / (n : ℝ) = d
  genusLogconvexity :
    ∀ g : ℕ, 1 ≤ g →
      conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition_core
          n dm g ^ 2 ≤
        conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition_core
            n dm (g - 1) *
          conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition_core
            n dm (g + 1)
  logconvexityRigidity :
    ∀ g : ℕ, 1 ≤ g →
      conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition_core
          n dm g ^ 2 =
        conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition_core
            n dm (g - 1) *
          conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition_core
            n dm (g + 1) →
        ∃ d : ℕ, 1 ≤ d ∧ ∀ x : Fin n, dm x = d

namespace conclusion_tqft_genus_strict_logconvexity_nonintegral_average_Data

/-- The normalized genus partition function for the concrete profile. -/
noncomputable def conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition
    (D : conclusion_tqft_genus_strict_logconvexity_nonintegral_average_Data) (g : ℕ) : ℝ :=
  conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition_core D.n D.dm g

/-- Strict logconvexity at every positive genus. -/
def strictLogConvexAllGenus
    (D : conclusion_tqft_genus_strict_logconvexity_nonintegral_average_Data) : Prop :=
  ∀ g : ℕ, 1 ≤ g →
    D.conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition g ^ 2 <
      D.conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition (g - 1) *
        D.conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition (g + 1)

end conclusion_tqft_genus_strict_logconvexity_nonintegral_average_Data

/-- Paper label: `cor:conclusion-tqft-genus-strict-logconvexity-nonintegral-average`.
If equality held at a positive genus, rigidity would make all fiber multiplicities equal to an
integer `d`; the total-multiplicity identity would then make the average multiplicity integral,
contradicting the hypothesis. -/
theorem paper_conclusion_tqft_genus_strict_logconvexity_nonintegral_average
    (D : conclusion_tqft_genus_strict_logconvexity_nonintegral_average_Data) :
    D.strictLogConvexAllGenus := by
  intro g hg
  let Z :=
    D.conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition
  have hle : Z g ^ 2 ≤ Z (g - 1) * Z (g + 1) := by
    simpa [Z,
      conclusion_tqft_genus_strict_logconvexity_nonintegral_average_Data.conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition] using
      D.genusLogconvexity g hg
  have hne : Z g ^ 2 ≠ Z (g - 1) * Z (g + 1) := by
    intro heq
    rcases D.logconvexityRigidity g hg (by
      simpa [Z,
        conclusion_tqft_genus_strict_logconvexity_nonintegral_average_Data.conclusion_tqft_genus_strict_logconvexity_nonintegral_average_partition] using heq) with
      ⟨d, hd_pos, hd_const⟩
    have hn_ne : (D.n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt D.nonempty
    have htotal_real :
        (∑ x : Fin D.n, (D.dm x : ℝ)) = (2 : ℝ) ^ D.m := by
      exact_mod_cast D.totalMultiplicity
    have hsum_const :
        (∑ x : Fin D.n, (D.dm x : ℝ)) = (D.n : ℝ) * (d : ℝ) := by
      simp [hd_const]
    have havg : ((2 : ℝ) ^ D.m) / (D.n : ℝ) = d := by
      field_simp [hn_ne]
      nlinarith
    exact D.nonintegralAverage ⟨d, hd_pos, havg⟩
  exact lt_of_le_of_ne hle hne

end Omega.Conclusion

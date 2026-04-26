import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-finite-moment-spectrum-strict-determinacy-truncation`. -/
theorem paper_conclusion_finite_moment_spectrum_strict_determinacy_truncation {M : Nat}
    (hM : 0 < M) {h h' : Fin M -> Nat}
    (hmom : ∀ n : Fin M,
      (∑ t : Fin M, h t * (t.1 + 1) ^ (n.1 + 1)) =
        (∑ t : Fin M, h' t * (t.1 + 1) ^ (n.1 + 1))) :
    h = h' := by
  let _ := hM
  have hinj : Function.Injective (fun t : Fin M ↦ ((t.1 + 1 : Nat) : ℚ)) := by
    intro a b hab
    apply Fin.ext
    have habQ : ((a : ℚ) + 1) = (b : ℚ) + 1 := by
      simpa using hab
    have habVal : (a : ℚ) = b := by
      linarith
    exact_mod_cast habVal
  have hzero :
      ∀ n : Fin M,
        (∑ t : Fin M, ((((h t : ℚ) - h' t) * (((t.1 + 1 : Nat) : ℚ))) *
          (((t.1 + 1 : Nat) : ℚ) ^ (n : ℕ)))) = 0 := by
    intro n
    have hcast :
        (∑ t : Fin M, (h t : ℚ) * (((t.1 + 1 : Nat) : ℚ) ^ (n.1 + 1))) =
          ∑ t : Fin M, (h' t : ℚ) * (((t.1 + 1 : Nat) : ℚ) ^ (n.1 + 1)) := by
      exact_mod_cast hmom n
    have hsub :
        (∑ t : Fin M, ((h t : ℚ) - h' t) * (((t.1 + 1 : Nat) : ℚ) ^ (n.1 + 1))) = 0 := by
      simpa [Finset.sum_sub_distrib, sub_mul] using sub_eq_zero.mpr hcast
    simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using hsub
  have hv :
      (fun t : Fin M ↦ (((h t : ℚ) - h' t) * (((t.1 + 1 : Nat) : ℚ)))) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj hzero
  funext t
  have hprod := congrFun hv t
  have ht_ne : (((t.1 + 1 : Nat) : ℚ)) ≠ 0 := by positivity
  have hdiff : ((h t : ℚ) - h' t) = 0 := by
    rcases mul_eq_zero.mp hprod with hleft | hright
    · exact hleft
    · exact (ht_ne hright).elim
  exact_mod_cast (sub_eq_zero.mp hdiff)

end Omega.Conclusion
